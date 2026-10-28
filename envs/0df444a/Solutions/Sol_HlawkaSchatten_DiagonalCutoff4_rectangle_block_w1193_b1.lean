-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:15.008346+00:00
-- url     : https://prove2.me/submissions/fbdeff08-fb46-4631-bdb1-9273773eafd1

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
theorem support_rectangle_w1193_s3_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106972703/500000000 : ℝ)*x 0 + (5424124481/10000000000 : ℝ)*x 1 + (5236654929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106972703/500000000 : ℝ)^4193 ≤ (12998808477251/100000000000000 : ℝ)^3169 := by
    have hnat : (106972703 : ℕ)^4193*100000000000000^3169 ≤ 12998808477251^3169*500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106972703 500000000 12998808477251 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424124481/10000000000 : ℝ)^4193 ≤ (22256327582181/50000000000000 : ℝ)^3169 := by
    have hnat : (5424124481 : ℕ)^4193*50000000000000^3169 ≤ 22256327582181^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424124481 10000000000 22256327582181 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236654929/10000000000 : ℝ)^4193 ≤ (849770726853/2000000000000 : ℝ)^3169 := by
    have hnat : (5236654929 : ℕ)^4193*2000000000000^3169 ≤ 849770726853^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236654929 10000000000 849770726853 2000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106972703/500000000 : ℝ), (5424124481/10000000000 : ℝ), (5236654929/10000000000 : ℝ)] ![(12998808477251/100000000000000 : ℝ), (22256327582181/50000000000000 : ℝ), (849770726853/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106972703/500000000 : ℝ)|^4193 ≤ (12998808477251/100000000000000 : ℝ)^3169
        have hw : |(-106972703/500000000 : ℝ)|=(106972703/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424124481/10000000000 : ℝ)|^4193 ≤ (22256327582181/50000000000000 : ℝ)^3169
        have hw : |(5424124481/10000000000 : ℝ)|=(5424124481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236654929/10000000000 : ℝ)|^4193 ≤ (849770726853/2000000000000 : ℝ)^3169
        have hw : |(5236654929/10000000000 : ℝ)|=(5236654929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352592379/10000000000 : ℝ)*x 0 + (-2235179279/10000000000 : ℝ)*x 1 + (5236655179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352592379/10000000000 : ℝ)^4193 ≤ (8747521519579/20000000000000 : ℝ)^3169 := by
    have hnat : (5352592379 : ℕ)^4193*20000000000000^3169 ≤ 8747521519579^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352592379 10000000000 8747521519579 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235179279/10000000000 : ℝ)^4193 ≤ (13773853357339/100000000000000 : ℝ)^3169 := by
    have hnat : (2235179279 : ℕ)^4193*100000000000000^3169 ≤ 13773853357339^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235179279 10000000000 13773853357339 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236655179/10000000000 : ℝ)^4193 ≤ (21244269513257/50000000000000 : ℝ)^3169 := by
    have hnat : (5236655179 : ℕ)^4193*50000000000000^3169 ≤ 21244269513257^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236655179 10000000000 21244269513257 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352592379/10000000000 : ℝ), (-2235179279/10000000000 : ℝ), (5236655179/10000000000 : ℝ)] ![(8747521519579/20000000000000 : ℝ), (13773853357339/100000000000000 : ℝ), (21244269513257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352592379/10000000000 : ℝ)|^4193 ≤ (8747521519579/20000000000000 : ℝ)^3169
        have hw : |(5352592379/10000000000 : ℝ)|=(5352592379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235179279/10000000000 : ℝ)|^4193 ≤ (13773853357339/100000000000000 : ℝ)^3169
        have hw : |(-2235179279/10000000000 : ℝ)|=(2235179279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236655179/10000000000 : ℝ)|^4193 ≤ (21244269513257/50000000000000 : ℝ)^3169
        have hw : |(5236655179/10000000000 : ℝ)|=(5236655179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676296121/5000000000 : ℝ)*x 0 + (1309163859/2500000000 : ℝ)*x 1 + (-2235179123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676296121/5000000000 : ℝ)^4193 ≤ (21868803058347/50000000000000 : ℝ)^3169 := by
    have hnat : (2676296121 : ℕ)^4193*50000000000000^3169 ≤ 21868803058347^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676296121 5000000000 21868803058347 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309163859/2500000000 : ℝ)^4193 ≤ (1699541671421/4000000000000 : ℝ)^3169 := by
    have hnat : (1309163859 : ℕ)^4193*4000000000000^3169 ≤ 1699541671421^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309163859 2500000000 1699541671421 4000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2235179123/10000000000 : ℝ)^4193 ≤ (13773852085389/100000000000000 : ℝ)^3169 := by
    have hnat : (2235179123 : ℕ)^4193*100000000000000^3169 ≤ 13773852085389^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235179123 10000000000 13773852085389 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676296121/5000000000 : ℝ), (1309163859/2500000000 : ℝ), (-2235179123/10000000000 : ℝ)] ![(21868803058347/50000000000000 : ℝ), (1699541671421/4000000000000 : ℝ), (13773852085389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676296121/5000000000 : ℝ)|^4193 ≤ (21868803058347/50000000000000 : ℝ)^3169
        have hw : |(2676296121/5000000000 : ℝ)|=(2676296121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309163859/2500000000 : ℝ)|^4193 ≤ (1699541671421/4000000000000 : ℝ)^3169
        have hw : |(1309163859/2500000000 : ℝ)|=(1309163859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2235179123/10000000000 : ℝ)|^4193 ≤ (13773852085389/100000000000000 : ℝ)^3169
        have hw : |(-2235179123/10000000000 : ℝ)|=(2235179123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544448107/1250000000 : ℝ)*x 0 + (4171234951/10000000000 : ℝ)*x 1 + (1136983663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544448107/1250000000 : ℝ)^4193 ≤ (16648743215613/50000000000000 : ℝ)^3169 := by
    have hnat : (544448107 : ℕ)^4193*50000000000000^3169 ≤ 16648743215613^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544448107 1250000000 16648743215613 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171234951/10000000000 : ℝ)^4193 ≤ (31445655095883/100000000000000 : ℝ)^3169 := by
    have hnat : (4171234951 : ℕ)^4193*100000000000000^3169 ≤ 31445655095883^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171234951 10000000000 31445655095883 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136983663/2500000000 : ℝ)^4193 ≤ (17628429229437/50000000000000 : ℝ)^3169 := by
    have hnat : (1136983663 : ℕ)^4193*50000000000000^3169 ≤ 17628429229437^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136983663 2500000000 17628429229437 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544448107/1250000000 : ℝ), (4171234951/10000000000 : ℝ), (1136983663/2500000000 : ℝ)] ![(16648743215613/50000000000000 : ℝ), (31445655095883/100000000000000 : ℝ), (17628429229437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544448107/1250000000 : ℝ)|^4193 ≤ (16648743215613/50000000000000 : ℝ)^3169
        have hw : |(544448107/1250000000 : ℝ)|=(544448107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171234951/10000000000 : ℝ)|^4193 ≤ (31445655095883/100000000000000 : ℝ)^3169
        have hw : |(4171234951/10000000000 : ℝ)|=(4171234951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136983663/2500000000 : ℝ)|^4193 ≤ (17628429229437/50000000000000 : ℝ)^3169
        have hw : |(1136983663/2500000000 : ℝ)|=(1136983663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-534867507/2500000000 : ℝ)*x 0 + (2618678963/5000000000 : ℝ)*x 1 + (677927197/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534867507/2500000000 : ℝ)^4193 ≤ (2599787368901/20000000000000 : ℝ)^3169 := by
    have hnat : (534867507 : ℕ)^4193*20000000000000^3169 ≤ 2599787368901^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534867507 2500000000 2599787368901 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618678963/5000000000 : ℝ)^4193 ≤ (21248041749333/50000000000000 : ℝ)^3169 := by
    have hnat : (2618678963 : ℕ)^4193*50000000000000^3169 ≤ 21248041749333^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618678963 5000000000 21248041749333 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677927197/1250000000 : ℝ)^4193 ≤ (44504979634167/100000000000000 : ℝ)^3169 := by
    have hnat : (677927197 : ℕ)^4193*100000000000000^3169 ≤ 44504979634167^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677927197 1250000000 44504979634167 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534867507/2500000000 : ℝ), (2618678963/5000000000 : ℝ), (677927197/1250000000 : ℝ)] ![(2599787368901/20000000000000 : ℝ), (21248041749333/50000000000000 : ℝ), (44504979634167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534867507/2500000000 : ℝ)|^4193 ≤ (2599787368901/20000000000000 : ℝ)^3169
        have hw : |(-534867507/2500000000 : ℝ)|=(534867507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618678963/5000000000 : ℝ)|^4193 ≤ (21248041749333/50000000000000 : ℝ)^3169
        have hw : |(2618678963/5000000000 : ℝ)|=(2618678963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677927197/1250000000 : ℝ)|^4193 ≤ (44504979634167/100000000000000 : ℝ)^3169
        have hw : |(677927197/1250000000 : ℝ)|=(677927197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652462469/5000000000 : ℝ)*x 0 + (-1024208239/5000000000 : ℝ)*x 1 + (2711708753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652462469/5000000000 : ℝ)^4193 ≤ (43222985144013/100000000000000 : ℝ)^3169 := by
    have hnat : (2652462469 : ℕ)^4193*100000000000000^3169 ≤ 43222985144013^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652462469 5000000000 43222985144013 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024208239/5000000000 : ℝ)^4193 ≤ (3068008992503/25000000000000 : ℝ)^3169 := by
    have hnat : (1024208239 : ℕ)^4193*25000000000000^3169 ≤ 3068008992503^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024208239 5000000000 3068008992503 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711708753/5000000000 : ℝ)^4193 ≤ (2781561179633/6250000000000 : ℝ)^3169 := by
    have hnat : (2711708753 : ℕ)^4193*6250000000000^3169 ≤ 2781561179633^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711708753 5000000000 2781561179633 6250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652462469/5000000000 : ℝ), (-1024208239/5000000000 : ℝ), (2711708753/5000000000 : ℝ)] ![(43222985144013/100000000000000 : ℝ), (3068008992503/25000000000000 : ℝ), (2781561179633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652462469/5000000000 : ℝ)|^4193 ≤ (43222985144013/100000000000000 : ℝ)^3169
        have hw : |(2652462469/5000000000 : ℝ)|=(2652462469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024208239/5000000000 : ℝ)|^4193 ≤ (3068008992503/25000000000000 : ℝ)^3169
        have hw : |(-1024208239/5000000000 : ℝ)|=(1024208239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711708753/5000000000 : ℝ)|^4193 ≤ (2781561179633/6250000000000 : ℝ)^3169
        have hw : |(2711708753/5000000000 : ℝ)|=(2711708753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304924563/10000000000 : ℝ)*x 0 + (5423417911/10000000000 : ℝ)*x 1 + (-2048416433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304924563/10000000000 : ℝ)^4193 ≤ (10805745275333/25000000000000 : ℝ)^3169 := by
    have hnat : (5304924563 : ℕ)^4193*25000000000000^3169 ≤ 10805745275333^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304924563 10000000000 10805745275333 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423417911/10000000000 : ℝ)^4193 ≤ (89009966543/200000000000 : ℝ)^3169 := by
    have hnat : (5423417911 : ℕ)^4193*200000000000^3169 ≤ 89009966543^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423417911 10000000000 89009966543 200000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048416433/10000000000 : ℝ)^4193 ≤ (12272035613303/100000000000000 : ℝ)^3169 := by
    have hnat : (2048416433 : ℕ)^4193*100000000000000^3169 ≤ 12272035613303^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048416433 10000000000 12272035613303 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304924563/10000000000 : ℝ), (5423417911/10000000000 : ℝ), (-2048416433/10000000000 : ℝ)] ![(10805745275333/25000000000000 : ℝ), (89009966543/200000000000 : ℝ), (12272035613303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304924563/10000000000 : ℝ)|^4193 ≤ (10805745275333/25000000000000 : ℝ)^3169
        have hw : |(5304924563/10000000000 : ℝ)|=(5304924563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423417911/10000000000 : ℝ)|^4193 ≤ (89009966543/200000000000 : ℝ)^3169
        have hw : |(5423417911/10000000000 : ℝ)|=(5423417911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048416433/10000000000 : ℝ)|^4193 ≤ (12272035613303/100000000000000 : ℝ)^3169
        have hw : |(-2048416433/10000000000 : ℝ)|=(2048416433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s3_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871123427/2000000000 : ℝ)*x 0 + (2273260887/5000000000 : ℝ)*x 1 + (166906199/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871123427/2000000000 : ℝ)^4193 ≤ (6659562586997/20000000000000 : ℝ)^3169 := by
    have hnat : (871123427 : ℕ)^4193*20000000000000^3169 ≤ 6659562586997^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871123427 2000000000 6659562586997 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273260887/5000000000 : ℝ)^4193 ≤ (17621183453731/50000000000000 : ℝ)^3169 := by
    have hnat : (2273260887 : ℕ)^4193*50000000000000^3169 ≤ 17621183453731^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273260887 5000000000 17621183453731 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166906199/400000000 : ℝ)^4193 ≤ (15729910074153/50000000000000 : ℝ)^3169 := by
    have hnat : (166906199 : ℕ)^4193*50000000000000^3169 ≤ 15729910074153^3169*400000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166906199 400000000 15729910074153 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871123427/2000000000 : ℝ), (2273260887/5000000000 : ℝ), (166906199/400000000 : ℝ)] ![(6659562586997/20000000000000 : ℝ), (17621183453731/50000000000000 : ℝ), (15729910074153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871123427/2000000000 : ℝ)|^4193 ≤ (6659562586997/20000000000000 : ℝ)^3169
        have hw : |(871123427/2000000000 : ℝ)|=(871123427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2273260887/5000000000 : ℝ)|^4193 ≤ (17621183453731/50000000000000 : ℝ)^3169
        have hw : |(2273260887/5000000000 : ℝ)|=(2273260887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166906199/400000000 : ℝ)|^4193 ≤ (15729910074153/50000000000000 : ℝ)^3169
        have hw : |(166906199/400000000 : ℝ)|=(166906199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10781/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3271/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1859/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3271/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1859/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3271/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1859/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3271/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1859/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3271/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1859/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3271/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1859/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1859/20000 : ℝ) ^ (8385/2048 : ℝ) ≤ (5967152988959637/100000000000000000000 : ℝ) := by
    have hpowers : (1859/20000 : ℝ)^8385 ≤ (5967152988959637/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1859 : ℕ)^8385*100000000000000000000^2048 ≤ 5967152988959637^2048*20000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1859 20000 5967152988959637 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1859/20000 : ℝ)) (X := (5967152988959637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3271/20000 : ℝ) ^ (8385/2048 : ℝ) ≤ (60325089243899563/100000000000000000000 : ℝ) := by
    have hpowers : (3271/20000 : ℝ)^8385 ≤ (60325089243899563/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3271 : ℕ)^8385*100000000000000000000^2048 ≤ 60325089243899563^2048*20000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3271 20000 60325089243899563 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3271/20000 : ℝ)) (X := (60325089243899563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005967152988959637/50000000000000000000 : ℝ) ≤ (10000291477119653/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50005967152988959637/50000000000000000000 : ℝ)^2048 ≤ (10000291477119653/10000000000000000 : ℝ)^8385 := by
      have hnat : (50005967152988959637 : ℕ)^2048*10000000000000000^8385 ≤ 10000291477119653^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005967152988959637 50000000000000000000 10000291477119653 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000291477119653/10000000000000000 : ℝ)) (X := (50005967152988959637/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (62541432651395537/62500000000000000 : ℝ) ≤ (2500404688477431/2500000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (62541432651395537/62500000000000000 : ℝ)^2048 ≤ (2500404688477431/2500000000000000 : ℝ)^8385 := by
      have hnat : (62541432651395537 : ℕ)^2048*2500000000000000^8385 ≤ 2500404688477431^8385*62500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62541432651395537 62500000000000000 2500404688477431 2500000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500404688477431/2500000000000000 : ℝ)) (X := (62541432651395537/62500000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50060325089243899563/50000000000000000000 : ℝ) ≤ (2000589206139959/2000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50060325089243899563/50000000000000000000 : ℝ)^2048 ≤ (2000589206139959/2000000000000000 : ℝ)^8385 := by
      have hnat : (50060325089243899563 : ℕ)^2048*2000000000000000^8385 ≤ 2000589206139959^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50060325089243899563 50000000000000000000 2000589206139959 2000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000589206139959/2000000000000000 : ℝ)) (X := (50060325089243899563/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5967152988959637/100000000000000000000 : ℝ) ≤ ((7057738375293733029/7060000000000000000 : ℝ)+2*(1327276790071/706000000000000 : ℝ)*(1859/20000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (7057738375293733029/7060000000000000000 : ℝ)+2*(1327276790071/706000000000000 : ℝ)*(1859/20000 : ℝ)=(10000291477119653/10000000000000000 : ℝ) by norm_num, show 1+2*(5967152988959637/100000000000000000000 : ℝ)=(50005967152988959637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60325089243899563/100000000000000000000 : ℝ)+(5967152988959637/100000000000000000000 : ℝ) ≤ ((7057738375293733029/7060000000000000000 : ℝ)+(1327276790071/706000000000000 : ℝ)*((3271/20000 : ℝ)+(1859/20000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (7057738375293733029/7060000000000000000 : ℝ)+(1327276790071/706000000000000 : ℝ)*((3271/20000 : ℝ)+(1859/20000 : ℝ))=(2500404688477431/2500000000000000 : ℝ) by norm_num, show 1+(60325089243899563/100000000000000000000 : ℝ)+(5967152988959637/100000000000000000000 : ℝ)=(62541432651395537/62500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60325089243899563/100000000000000000000 : ℝ) ≤ ((7057738375293733029/7060000000000000000 : ℝ)+2*(1327276790071/706000000000000 : ℝ)*(3271/20000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (7057738375293733029/7060000000000000000 : ℝ)+2*(1327276790071/706000000000000 : ℝ)*(3271/20000 : ℝ)=(2000589206139959/2000000000000000 : ℝ) by norm_num, show 1+2*(60325089243899563/100000000000000000000 : ℝ)=(50060325089243899563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7057738375293733029/7060000000000000000 : ℝ)*(X 1 0+X 2 0)+(1327276790071/706000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (1859/20000 : ℝ)) (hi := (3271/20000 : ℝ)) (c := (7057738375293733029/7060000000000000000 : ℝ)) (alpha := (1327276790071/706000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7057738375293733029/7060000000000000000 : ℝ)*(X 0 1+X 2 1)+(1327276790071/706000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (1859/20000 : ℝ)) (hi := (3271/20000 : ℝ)) (c := (7057738375293733029/7060000000000000000 : ℝ)) (alpha := (1327276790071/706000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7057738375293733029/7060000000000000000 : ℝ)*(X 0 2+X 1 2)+(1327276790071/706000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (1859/20000 : ℝ)) (hi := (3271/20000 : ℝ)) (c := (7057738375293733029/7060000000000000000 : ℝ)) (alpha := (1327276790071/706000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106972703/500000000 : ℝ)*X 0 0+(5424124481/10000000000 : ℝ)*X 0 1+(5236654929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352592379/10000000000 : ℝ)*X 1 0+(-2235179279/10000000000 : ℝ)*X 1 1+(5236655179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676296121/5000000000 : ℝ)*X 2 0+(1309163859/2500000000 : ℝ)*X 2 1+(-2235179123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544448107/1250000000 : ℝ)*X 0 0+(4171234951/10000000000 : ℝ)*X 0 1+(1136983663/2500000000 : ℝ)*X 0 2+(544448107/1250000000 : ℝ)*X 1 0+(4171234951/10000000000 : ℝ)*X 1 1+(1136983663/2500000000 : ℝ)*X 1 2+(544448107/1250000000 : ℝ)*X 2 0+(4171234951/10000000000 : ℝ)*X 2 1+(1136983663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534867507/2500000000 : ℝ)*X 0 0+(2618678963/5000000000 : ℝ)*X 0 1+(677927197/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652462469/5000000000 : ℝ)*X 1 0+(-1024208239/5000000000 : ℝ)*X 1 1+(2711708753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304924563/10000000000 : ℝ)*X 2 0+(5423417911/10000000000 : ℝ)*X 2 1+(-2048416433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871123427/2000000000 : ℝ)*X 0 0+(2273260887/5000000000 : ℝ)*X 0 1+(166906199/400000000 : ℝ)*X 0 2+(871123427/2000000000 : ℝ)*X 1 0+(2273260887/5000000000 : ℝ)*X 1 1+(166906199/400000000 : ℝ)*X 1 2+(871123427/2000000000 : ℝ)*X 2 0+(2273260887/5000000000 : ℝ)*X 2 1+(166906199/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26143280409907157666577/3530000000000000000000000000 : ℝ) := by norm_num
    linear_combination (500688409/50000000000000 : ℝ)*(base19) + (707121399/100000000000000 : ℝ)*(base23) + (84423659/100000000000000 : ℝ)*(lower2) + (84916401/100000000000000 : ℝ)*(upper3) + (111476841/100000000000000 : ℝ)*(upper5) + (399445559196401/10000000000000 : ℝ)*(major0) + (399445559196401/10000000000000 : ℝ)*(major1) + (399445559196401/10000000000000 : ℝ)*(major2) + (5334225891698213/100000000000000 : ℝ)*(sp0) + (2667126511952621/50000000000000 : ℝ)*(sp1) + (5334253318160661/100000000000000 : ℝ)*(sp2) + (1327322877602639/50000000000000 : ℝ)*(sp3) + (3516697981/12500000000000 : ℝ)*(sp4) + (2231314611/20000000000000 : ℝ)*(sp7) + (1327328455889167/50000000000000 : ℝ)*(f.failure) + (266712701264103/5000000000000 : ℝ)*(f.sum) + (3225102746901/3530000000000000000000000000 : ℝ)*base65 + (580867957003061371/70600000000000000000000000000000 : ℝ)*base68 + (606809472127261371/70600000000000000000000000000000 : ℝ)*base70 + (425209191379738629/70600000000000000000000000000000 : ℝ)*base71 + (3226768483429/3530000000000000000000000000 : ℝ)*base74 + (669307131966938629/70600000000000000000000000000000 : ℝ)*base75 + (890128200446661371/70600000000000000000000000000000 : ℝ)*base78 + (2381411215449938629/70600000000000000000000000000000 : ℝ)*base79 + (18360871864131/3530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (30309083/5000000000000000000000 : ℝ)*base89 + (30309083/5000000000000000000000 : ℝ)*base91 + (30309083/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1729393236114457431533257737/176500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1289233937/50000000000000 : ℝ)*(base19) + (2504805003/100000000000000 : ℝ)*(base23) + (12099851/6250000000000 : ℝ)*(upper3) + (6134003/4000000000000 : ℝ)*(lower4) + (321929703/100000000000000 : ℝ)*(upper5) + (2012341243298951/50000000000000 : ℝ)*(major0) + (2012341243298951/50000000000000 : ℝ)*(major1) + (2012341243298951/50000000000000 : ℝ)*(major2) + (25402262791/50000000000000 : ℝ)*(sp1) + (52717613887/100000000000000 : ℝ)*(sp2) + (5374619381611647/100000000000000 : ℝ)*(sp4) + (5374565998618191/100000000000000 : ℝ)*(sp5) + (5374564159192757/100000000000000 : ℝ)*(sp6) + (1337372632487711/50000000000000 : ℝ)*(sp7) + (1337372632487711/50000000000000 : ℝ)*(f.failure) + (5374619381611647/100000000000000 : ℝ)*(f.sum) + (16188498092421/17650000000000000000000000000 : ℝ)*base65 + (2559821096234962579/353000000000000000000000000000000 : ℝ)*base67 + (286745972081037421/353000000000000000000000000000000 : ℝ)*base70 + (2565011708233037421/353000000000000000000000000000000 : ℝ)*base72 + (62321501562721/17650000000000000000000000000 : ℝ)*base73 + (789327525262962579/353000000000000000000000000000000 : ℝ)*base75 + (188816250710037421/353000000000000000000000000000000 : ℝ)*base78 + (918480725426037421/353000000000000000000000000000000 : ℝ)*base80 + (10031066059679/17650000000000000000000000000 : ℝ)*base82 + (19754539/5000000000000000000000 : ℝ)*base89 + (19754539/5000000000000000000000 : ℝ)*base91 + (19754539/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1193_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10781/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1193_s4_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071034347/5000000000 : ℝ)*x 0 + (1079911309/2000000000 : ℝ)*x 1 + (5259511083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071034347/5000000000 : ℝ)^4193 ≤ (2603966345173/20000000000000 : ℝ)^3169 := by
    have hnat : (1071034347 : ℕ)^4193*20000000000000^3169 ≤ 2603966345173^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071034347 5000000000 2603966345173 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079911309/2000000000 : ℝ)^4193 ≤ (8849217570371/20000000000000 : ℝ)^3169 := by
    have hnat : (1079911309 : ℕ)^4193*20000000000000^3169 ≤ 8849217570371^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079911309 2000000000 8849217570371 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259511083/10000000000 : ℝ)^4193 ≤ (427340804043/1000000000000 : ℝ)^3169 := by
    have hnat : (5259511083 : ℕ)^4193*1000000000000^3169 ≤ 427340804043^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259511083 10000000000 427340804043 1000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071034347/5000000000 : ℝ), (1079911309/2000000000 : ℝ), (5259511083/10000000000 : ℝ)] ![(2603966345173/20000000000000 : ℝ), (8849217570371/20000000000000 : ℝ), (427340804043/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071034347/5000000000 : ℝ)|^4193 ≤ (2603966345173/20000000000000 : ℝ)^3169
        have hw : |(-1071034347/5000000000 : ℝ)|=(1071034347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079911309/2000000000 : ℝ)|^4193 ≤ (8849217570371/20000000000000 : ℝ)^3169
        have hw : |(1079911309/2000000000 : ℝ)|=(1079911309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259511083/10000000000 : ℝ)|^4193 ≤ (427340804043/1000000000000 : ℝ)^3169
        have hw : |(5259511083/10000000000 : ℝ)|=(5259511083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673213881/5000000000 : ℝ)*x 0 + (-442640457/2000000000 : ℝ)*x 1 + (5259511171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673213881/5000000000 : ℝ)^4193 ≤ (21835485045911/50000000000000 : ℝ)^3169 := by
    have hnat : (2673213881 : ℕ)^4193*50000000000000^3169 ≤ 21835485045911^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673213881 5000000000 21835485045911 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442640457/2000000000 : ℝ)^4193 ≤ (13594948548449/100000000000000 : ℝ)^3169 := by
    have hnat : (442640457 : ℕ)^4193*100000000000000^3169 ≤ 13594948548449^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442640457 2000000000 13594948548449 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5259511171/10000000000 : ℝ)^4193 ≤ (854681627007/2000000000000 : ℝ)^3169 := by
    have hnat : (5259511171 : ℕ)^4193*2000000000000^3169 ≤ 854681627007^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259511171 10000000000 854681627007 2000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673213881/5000000000 : ℝ), (-442640457/2000000000 : ℝ), (5259511171/10000000000 : ℝ)] ![(21835485045911/50000000000000 : ℝ), (13594948548449/100000000000000 : ℝ), (854681627007/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673213881/5000000000 : ℝ)|^4193 ≤ (21835485045911/50000000000000 : ℝ)^3169
        have hw : |(2673213881/5000000000 : ℝ)|=(2673213881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442640457/2000000000 : ℝ)|^4193 ≤ (13594948548449/100000000000000 : ℝ)^3169
        have hw : |(-442640457/2000000000 : ℝ)|=(442640457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5259511171/10000000000 : ℝ)|^4193 ≤ (854681627007/2000000000000 : ℝ)^3169
        have hw : |(5259511171/10000000000 : ℝ)|=(5259511171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346427497/10000000000 : ℝ)*x 0 + (525951103/1000000000 : ℝ)*x 1 + (-2213202823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346427497/10000000000 : ℝ)^4193 ≤ (2729435451737/6250000000000 : ℝ)^3169 := by
    have hnat : (5346427497 : ℕ)^4193*6250000000000^3169 ≤ 2729435451737^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346427497 10000000000 2729435451737 6250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525951103/1000000000 : ℝ)^4193 ≤ (42734079834519/100000000000000 : ℝ)^3169 := by
    have hnat : (525951103 : ℕ)^4193*100000000000000^3169 ≤ 42734079834519^3169*1000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525951103 1000000000 42734079834519 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213202823/10000000000 : ℝ)^4193 ≤ (2718990584213/20000000000000 : ℝ)^3169 := by
    have hnat : (2213202823 : ℕ)^4193*20000000000000^3169 ≤ 2718990584213^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213202823 10000000000 2718990584213 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346427497/10000000000 : ℝ), (525951103/1000000000 : ℝ), (-2213202823/10000000000 : ℝ)] ![(2729435451737/6250000000000 : ℝ), (42734079834519/100000000000000 : ℝ), (2718990584213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346427497/10000000000 : ℝ)|^4193 ≤ (2729435451737/6250000000000 : ℝ)^3169
        have hw : |(5346427497/10000000000 : ℝ)|=(5346427497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525951103/1000000000 : ℝ)|^4193 ≤ (42734079834519/100000000000000 : ℝ)^3169
        have hw : |(525951103/1000000000 : ℝ)|=(525951103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213202823/10000000000 : ℝ)|^4193 ≤ (2718990584213/20000000000000 : ℝ)^3169
        have hw : |(-2213202823/10000000000 : ℝ)|=(2213202823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178575113/5000000000 : ℝ)*x 0 + (131833737/312500000 : ℝ)*x 1 + (900017469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178575113/5000000000 : ℝ)^4193 ≤ (16656660565177/50000000000000 : ℝ)^3169 := by
    have hnat : (2178575113 : ℕ)^4193*50000000000000^3169 ≤ 16656660565177^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178575113 5000000000 16656660565177 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131833737/312500000 : ℝ)^4193 ≤ (3989970899079/12500000000000 : ℝ)^3169 := by
    have hnat : (131833737 : ℕ)^4193*12500000000000^3169 ≤ 3989970899079^3169*312500000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131833737 312500000 3989970899079 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900017469/2000000000 : ℝ)^4193 ≤ (1738345582941/5000000000000 : ℝ)^3169 := by
    have hnat : (900017469 : ℕ)^4193*5000000000000^3169 ≤ 1738345582941^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900017469 2000000000 1738345582941 5000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178575113/5000000000 : ℝ), (131833737/312500000 : ℝ), (900017469/2000000000 : ℝ)] ![(16656660565177/50000000000000 : ℝ), (3989970899079/12500000000000 : ℝ), (1738345582941/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178575113/5000000000 : ℝ)|^4193 ≤ (16656660565177/50000000000000 : ℝ)^3169
        have hw : |(2178575113/5000000000 : ℝ)|=(2178575113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131833737/312500000 : ℝ)|^4193 ≤ (3989970899079/12500000000000 : ℝ)^3169
        have hw : |(131833737/312500000 : ℝ)|=(131833737/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900017469/2000000000 : ℝ)|^4193 ≤ (1738345582941/5000000000000 : ℝ)^3169
        have hw : |(900017469/2000000000 : ℝ)|=(900017469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214207509/1000000000 : ℝ)*x 0 + (1314975951/2500000000 : ℝ)*x 1 + (5399162391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214207509/1000000000 : ℝ)^4193 ≤ (13019883163769/100000000000000 : ℝ)^3169 := by
    have hnat : (214207509 : ℕ)^4193*100000000000000^3169 ≤ 13019883163769^3169*1000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214207509 1000000000 13019883163769 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314975951/2500000000 : ℝ)^4193 ≤ (42738302431/100000000000 : ℝ)^3169 := by
    have hnat : (1314975951 : ℕ)^4193*100000000000^3169 ≤ 42738302431^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314975951 2500000000 42738302431 100000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399162391/10000000000 : ℝ)^4193 ≤ (44241814386149/100000000000000 : ℝ)^3169 := by
    have hnat : (5399162391 : ℕ)^4193*100000000000000^3169 ≤ 44241814386149^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399162391 10000000000 44241814386149 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214207509/1000000000 : ℝ), (1314975951/2500000000 : ℝ), (5399162391/10000000000 : ℝ)] ![(13019883163769/100000000000000 : ℝ), (42738302431/100000000000 : ℝ), (44241814386149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214207509/1000000000 : ℝ)|^4193 ≤ (13019883163769/100000000000000 : ℝ)^3169
        have hw : |(-214207509/1000000000 : ℝ)|=(214207509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314975951/2500000000 : ℝ)|^4193 ≤ (42738302431/100000000000 : ℝ)^3169
        have hw : |(1314975951/2500000000 : ℝ)|=(1314975951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399162391/10000000000 : ℝ)|^4193 ≤ (44241814386149/100000000000000 : ℝ)^3169
        have hw : |(5399162391/10000000000 : ℝ)|=(5399162391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6638521/12500000 : ℝ)*x 0 + (-16199621/78125000 : ℝ)*x 1 + (2699581217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6638521/12500000 : ℝ)^4193 ≤ (338175887851/781250000000 : ℝ)^3169 := by
    have hnat : (6638521 : ℕ)^4193*781250000000^3169 ≤ 338175887851^3169*12500000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6638521 12500000 338175887851 781250000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16199621/78125000 : ℝ)^4193 ≤ (623583574259/5000000000000 : ℝ)^3169 := by
    have hnat : (16199621 : ℕ)^4193*5000000000000^3169 ≤ 623583574259^3169*78125000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16199621 78125000 623583574259 5000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699581217/5000000000 : ℝ)^4193 ≤ (22120907426177/50000000000000 : ℝ)^3169 := by
    have hnat : (2699581217 : ℕ)^4193*50000000000000^3169 ≤ 22120907426177^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699581217 5000000000 22120907426177 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6638521/12500000 : ℝ), (-16199621/78125000 : ℝ), (2699581217/5000000000 : ℝ)] ![(338175887851/781250000000 : ℝ), (623583574259/5000000000000 : ℝ), (22120907426177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6638521/12500000 : ℝ)|^4193 ≤ (338175887851/781250000000 : ℝ)^3169
        have hw : |(6638521/12500000 : ℝ)|=(6638521/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16199621/78125000 : ℝ)|^4193 ≤ (623583574259/5000000000000 : ℝ)^3169
        have hw : |(-16199621/78125000 : ℝ)|=(16199621/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699581217/5000000000 : ℝ)|^4193 ≤ (22120907426177/50000000000000 : ℝ)^3169
        have hw : |(2699581217/5000000000 : ℝ)|=(2699581217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310817133/10000000000 : ℝ)*x 0 + (1079832423/2000000000 : ℝ)*x 1 + (-2073551473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310817133/10000000000 : ℝ)^4193 ≤ (43286517236117/100000000000000 : ℝ)^3169 := by
    have hnat : (5310817133 : ℕ)^4193*100000000000000^3169 ≤ 43286517236117^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310817133 10000000000 43286517236117 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079832423/2000000000 : ℝ)^4193 ≤ (22120905696879/50000000000000 : ℝ)^3169 := by
    have hnat : (1079832423 : ℕ)^4193*50000000000000^3169 ≤ 22120905696879^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079832423 2000000000 22120905696879 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073551473/10000000000 : ℝ)^4193 ≤ (779479460363/6250000000000 : ℝ)^3169 := by
    have hnat : (2073551473 : ℕ)^4193*6250000000000^3169 ≤ 779479460363^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073551473 10000000000 779479460363 6250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310817133/10000000000 : ℝ), (1079832423/2000000000 : ℝ), (-2073551473/10000000000 : ℝ)] ![(43286517236117/100000000000000 : ℝ), (22120905696879/50000000000000 : ℝ), (779479460363/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310817133/10000000000 : ℝ)|^4193 ≤ (43286517236117/100000000000000 : ℝ)^3169
        have hw : |(5310817133/10000000000 : ℝ)|=(5310817133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079832423/2000000000 : ℝ)|^4193 ≤ (22120905696879/50000000000000 : ℝ)^3169
        have hw : |(1079832423/2000000000 : ℝ)|=(1079832423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073551473/10000000000 : ℝ)|^4193 ≤ (779479460363/6250000000000 : ℝ)^3169
        have hw : |(-2073551473/10000000000 : ℝ)|=(2073551473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s4_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871432703/2000000000 : ℝ)*x 0 + (179971901/400000000 : ℝ)*x 1 + (4219472583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871432703/2000000000 : ℝ)^4193 ≤ (4164181945599/12500000000000 : ℝ)^3169 := by
    have hnat : (871432703 : ℕ)^4193*12500000000000^3169 ≤ 4164181945599^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871432703 2000000000 4164181945599 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179971901/400000000 : ℝ)^4193 ≤ (8689709531547/25000000000000 : ℝ)^3169 := by
    have hnat : (179971901 : ℕ)^4193*25000000000000^3169 ≤ 8689709531547^3169*400000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179971901 400000000 8689709531547 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219472583/10000000000 : ℝ)^4193 ≤ (31927706299089/100000000000000 : ℝ)^3169 := by
    have hnat : (4219472583 : ℕ)^4193*100000000000000^3169 ≤ 31927706299089^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219472583 10000000000 31927706299089 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871432703/2000000000 : ℝ), (179971901/400000000 : ℝ), (4219472583/10000000000 : ℝ)] ![(4164181945599/12500000000000 : ℝ), (8689709531547/25000000000000 : ℝ), (31927706299089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871432703/2000000000 : ℝ)|^4193 ≤ (4164181945599/12500000000000 : ℝ)^3169
        have hw : |(871432703/2000000000 : ℝ)|=(871432703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179971901/400000000 : ℝ)|^4193 ≤ (8689709531547/25000000000000 : ℝ)^3169
        have hw : |(179971901/400000000 : ℝ)|=(179971901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219472583/10000000000 : ℝ)|^4193 ≤ (31927706299089/100000000000000 : ℝ)^3169
        have hw : |(4219472583/10000000000 : ℝ)|=(4219472583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10781/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (10781/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10781/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10781/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10781/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10781/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10781/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10781/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (10951551134144477/100000000000000000000 : ℝ) := by
    have hpowers : (10781/100000 : ℝ)^8385 ≤ (10951551134144477/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10781 : ℕ)^8385*100000000000000000000^2048 ≤ 10951551134144477^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10781 100000 10951551134144477 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10781/100000 : ℝ)) (X := (10951551134144477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (7902161694020717/20000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^8385 ≤ (7902161694020717/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14749 : ℕ)^8385*20000000000000000000^2048 ≤ 7902161694020717^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 7902161694020717 20000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (7902161694020717/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010951551134144477/50000000000000000000 : ℝ) ≤ (10000534929531357/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50010951551134144477/50000000000000000000 : ℝ)^2048 ≤ (10000534929531357/10000000000000000 : ℝ)^8385 := by
      have hnat : (50010951551134144477 : ℕ)^2048*10000000000000000^8385 ≤ 10000534929531357^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010951551134144477 50000000000000000000 10000534929531357 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534929531357/10000000000000000 : ℝ)) (X := (50010951551134144477/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025231179802124031/50000000000000000000 : ℝ) ≤ (5000616143181311/5000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50025231179802124031/50000000000000000000 : ℝ)^2048 ≤ (5000616143181311/5000000000000000 : ℝ)^8385 := by
      have hnat : (50025231179802124031 : ℕ)^2048*5000000000000000^8385 ≤ 5000616143181311^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025231179802124031 50000000000000000000 5000616143181311 5000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000616143181311/5000000000000000 : ℝ)) (X := (50025231179802124031/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007902161694020717/10000000000000000000 : ℝ) ≤ (10001929643193887/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (10007902161694020717/10000000000000000000 : ℝ)^2048 ≤ (10001929643193887/10000000000000000 : ℝ)^8385 := by
      have hnat : (10007902161694020717 : ℕ)^2048*10000000000000000^8385 ≤ 10001929643193887^8385*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007902161694020717 10000000000000000000 10001929643193887 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001929643193887/10000000000000000 : ℝ)) (X := (10007902161694020717/10000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10951551134144477/100000000000000000000 : ℝ) ≤ ((19833543096192344323/19840000000000000000 : ℝ)+2*(139471366253/79360000000000 : ℝ)*(10781/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (19833543096192344323/19840000000000000000 : ℝ)+2*(139471366253/79360000000000 : ℝ)*(10781/100000 : ℝ)=(10000534929531357/10000000000000000 : ℝ) by norm_num, show 1+2*(10951551134144477/100000000000000000000 : ℝ)=(50010951551134144477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7902161694020717/20000000000000000000 : ℝ)+(10951551134144477/100000000000000000000 : ℝ) ≤ ((19833543096192344323/19840000000000000000 : ℝ)+(139471366253/79360000000000 : ℝ)*((14749/100000 : ℝ)+(10781/100000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (19833543096192344323/19840000000000000000 : ℝ)+(139471366253/79360000000000 : ℝ)*((14749/100000 : ℝ)+(10781/100000 : ℝ))=(5000616143181311/5000000000000000 : ℝ) by norm_num, show 1+(7902161694020717/20000000000000000000 : ℝ)+(10951551134144477/100000000000000000000 : ℝ)=(50025231179802124031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7902161694020717/20000000000000000000 : ℝ) ≤ ((19833543096192344323/19840000000000000000 : ℝ)+2*(139471366253/79360000000000 : ℝ)*(14749/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (19833543096192344323/19840000000000000000 : ℝ)+2*(139471366253/79360000000000 : ℝ)*(14749/100000 : ℝ)=(10001929643193887/10000000000000000 : ℝ) by norm_num, show 1+2*(7902161694020717/20000000000000000000 : ℝ)=(10007902161694020717/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19833543096192344323/19840000000000000000 : ℝ)*(X 1 0+X 2 0)+(139471366253/79360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (10781/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (19833543096192344323/19840000000000000000 : ℝ)) (alpha := (139471366253/79360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19833543096192344323/19840000000000000000 : ℝ)*(X 0 1+X 2 1)+(139471366253/79360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (10781/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (19833543096192344323/19840000000000000000 : ℝ)) (alpha := (139471366253/79360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19833543096192344323/19840000000000000000 : ℝ)*(X 0 2+X 1 2)+(139471366253/79360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (10781/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (19833543096192344323/19840000000000000000 : ℝ)) (alpha := (139471366253/79360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071034347/5000000000 : ℝ)*X 0 0+(1079911309/2000000000 : ℝ)*X 0 1+(5259511083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673213881/5000000000 : ℝ)*X 1 0+(-442640457/2000000000 : ℝ)*X 1 1+(5259511171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346427497/10000000000 : ℝ)*X 2 0+(525951103/1000000000 : ℝ)*X 2 1+(-2213202823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178575113/5000000000 : ℝ)*X 0 0+(131833737/312500000 : ℝ)*X 0 1+(900017469/2000000000 : ℝ)*X 0 2+(2178575113/5000000000 : ℝ)*X 1 0+(131833737/312500000 : ℝ)*X 1 1+(900017469/2000000000 : ℝ)*X 1 2+(2178575113/5000000000 : ℝ)*X 2 0+(131833737/312500000 : ℝ)*X 2 1+(900017469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214207509/1000000000 : ℝ)*X 0 0+(1314975951/2500000000 : ℝ)*X 0 1+(5399162391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((6638521/12500000 : ℝ)*X 1 0+(-16199621/78125000 : ℝ)*X 1 1+(2699581217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310817133/10000000000 : ℝ)*X 2 0+(1079832423/2000000000 : ℝ)*X 2 1+(-2073551473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871432703/2000000000 : ℝ)*X 0 0+(179971901/400000000 : ℝ)*X 0 1+(4219472583/10000000000 : ℝ)*X 0 2+(871432703/2000000000 : ℝ)*X 1 0+(179971901/400000000 : ℝ)*X 1 1+(4219472583/10000000000 : ℝ)*X 1 2+(871432703/2000000000 : ℝ)*X 2 0+(179971901/400000000 : ℝ)*X 2 1+(4219472583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (569767482549866643453572289/992000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1112926239/100000000000000 : ℝ)*(base19) + (505479477/50000000000000 : ℝ)*(base23) + (179789173/100000000000000 : ℝ)*(upper2) + (268266163/100000000000000 : ℝ)*(upper3) + (5347107654732281/100000000000000 : ℝ)*(major0) + (5347107654732281/100000000000000 : ℝ)*(major1) + (5347107654732281/100000000000000 : ℝ)*(major2) + (7140582482950467/100000000000000 : ℝ)*(sp0) + (1428120887675999/20000000000000 : ℝ)*(sp1) + (57124735050631/800000000000 : ℝ)*(sp2) + (177679262564173/5000000000000 : ℝ)*(sp3) + (23068355767/100000000000000 : ℝ)*(sp4) + (2531803681/20000000000000 : ℝ)*(sp6) + (489754589/2000000000000 : ℝ)*(sp7) + (355360973901291/10000000000000 : ℝ)*(f.failure) + (3570302775653117/50000000000000 : ℝ)*(f.sum) + (17859864268283/3968000000000000000000000000 : ℝ)*base66 + (808127116223559237/1984000000000000000000000000000000 : ℝ)*base68 + (6899749319936440763/1984000000000000000000000000000000 : ℝ)*base69 + (25165920948991559237/1984000000000000000000000000000000 : ℝ)*base72 + (7047078359173/3968000000000000000000000000 : ℝ)*base73 + (4457737022271559237/1984000000000000000000000000000000 : ℝ)*base76 + (18942088248191559237/1984000000000000000000000000000000 : ℝ)*base78 + (1940856378048440763/1984000000000000000000000000000000 : ℝ)*base79 + (19482770340613/3968000000000000000000000000 : ℝ)*base81 + (2454041/1000000000000000000000 : ℝ)*base90 + (2454041/1000000000000000000000 : ℝ)*base92 + (2454041/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (165420248049832675584244857/16000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1971415301/100000000000000 : ℝ)*(base19) + (2501919079/100000000000000 : ℝ)*(base23) + (33848397/20000000000000 : ℝ)*(upper3) + (45012351/100000000000000 : ℝ)*(lower4) + (344824609/100000000000000 : ℝ)*(upper5) + (2688639539501381/50000000000000 : ℝ)*(major0) + (2688639539501381/50000000000000 : ℝ)*(major1) + (2688639539501381/50000000000000 : ℝ)*(major2) + (55040821737/100000000000000 : ℝ)*(sp1) + (2718455437/5000000000000 : ℝ)*(sp2) + (7180896585964271/100000000000000 : ℝ)*(sp4) + (3506269323109/48828125000 : ℝ)*(sp5) + (1795209928734113/25000000000000 : ℝ)*(sp6) + (1786830613707863/50000000000000 : ℝ)*(sp7) + (1786830613707863/50000000000000 : ℝ)*(f.failure) + (7180896585964271/100000000000000 : ℝ)*(f.sum) + (326716146303/64000000000000000000000000 : ℝ)*base65 + (73893598032056127/32000000000000000000000000000000 : ℝ)*base68 + (635481027952056127/32000000000000000000000000000000 : ℝ)*base70 + (165894623632056127/32000000000000000000000000000000 : ℝ)*base72 + (109963481407/64000000000000000000000000 : ℝ)*base73 + (657733660080056127/32000000000000000000000000000000 : ℝ)*base76 + (482499286096056127/32000000000000000000000000000000 : ℝ)*base78 + (666832199504056127/32000000000000000000000000000000 : ℝ)*base80 + (8471118797/12800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4936387/5000000000000000000000 : ℝ)*base89 + (4936387/5000000000000000000000 : ℝ)*base91 + (4936387/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1193_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10781/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1193_s5_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-535650141/2500000000 : ℝ)*x 0 + (337100657/625000000 : ℝ)*x 1 + (52651079/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535650141/2500000000 : ℝ)^4193 ≤ (13024109299713/100000000000000 : ℝ)^3169 := by
    have hnat : (535650141 : ℕ)^4193*100000000000000^3169 ≤ 13024109299713^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535650141 2500000000 13024109299713 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337100657/625000000 : ℝ)^4193 ≤ (2761351934369/6250000000000 : ℝ)^3169 := by
    have hnat : (337100657 : ℕ)^4193*6250000000000^3169 ≤ 2761351934369^3169*625000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337100657 625000000 2761351934369 6250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52651079/100000000 : ℝ)^4193 ≤ (8558851947209/20000000000000 : ℝ)^3169 := by
    have hnat : (52651079 : ℕ)^4193*20000000000000^3169 ≤ 8558851947209^3169*100000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52651079 100000000 8558851947209 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535650141/2500000000 : ℝ), (337100657/625000000 : ℝ), (52651079/100000000 : ℝ)] ![(13024109299713/100000000000000 : ℝ), (2761351934369/6250000000000 : ℝ), (8558851947209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535650141/2500000000 : ℝ)|^4193 ≤ (13024109299713/100000000000000 : ℝ)^3169
        have hw : |(-535650141/2500000000 : ℝ)|=(535650141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337100657/625000000 : ℝ)|^4193 ≤ (2761351934369/6250000000000 : ℝ)^3169
        have hw : |(337100657/625000000 : ℝ)|=(337100657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52651079/100000000 : ℝ)|^4193 ≤ (8558851947209/20000000000000 : ℝ)^3169
        have hw : |(52651079/100000000 : ℝ)|=(52651079/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068985943/2000000000 : ℝ)*x 0 + (-551946961/2500000000 : ℝ)*x 1 + (1053021579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068985943/2000000000 : ℝ)^4193 ≤ (682105944359/1562500000000 : ℝ)^3169 := by
    have hnat : (1068985943 : ℕ)^4193*1562500000000^3169 ≤ 682105944359^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068985943 2000000000 682105944359 1562500000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551946961/2500000000 : ℝ)^4193 ≤ (6775479934719/50000000000000 : ℝ)^3169 := by
    have hnat : (551946961 : ℕ)^4193*50000000000000^3169 ≤ 6775479934719^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551946961 2500000000 6775479934719 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053021579/2000000000 : ℝ)^4193 ≤ (21397129841137/50000000000000 : ℝ)^3169 := by
    have hnat : (1053021579 : ℕ)^4193*50000000000000^3169 ≤ 21397129841137^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053021579 2000000000 21397129841137 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068985943/2000000000 : ℝ), (-551946961/2500000000 : ℝ), (1053021579/2000000000 : ℝ)] ![(682105944359/1562500000000 : ℝ), (6775479934719/50000000000000 : ℝ), (21397129841137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068985943/2000000000 : ℝ)|^4193 ≤ (682105944359/1562500000000 : ℝ)^3169
        have hw : |(1068985943/2000000000 : ℝ)|=(1068985943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551946961/2500000000 : ℝ)|^4193 ≤ (6775479934719/50000000000000 : ℝ)^3169
        have hw : |(-551946961/2500000000 : ℝ)|=(551946961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053021579/2000000000 : ℝ)|^4193 ≤ (21397129841137/50000000000000 : ℝ)^3169
        have hw : |(1053021579/2000000000 : ℝ)|=(1053021579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672464881/5000000000 : ℝ)*x 0 + (5265107867/10000000000 : ℝ)*x 1 + (-1103893909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672464881/5000000000 : ℝ)^4193 ≤ (4365478094689/10000000000000 : ℝ)^3169 := by
    have hnat : (2672464881 : ℕ)^4193*10000000000000^3169 ≤ 4365478094689^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672464881 5000000000 4365478094689 10000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265107867/10000000000 : ℝ)^4193 ≤ (8558851876231/20000000000000 : ℝ)^3169 := by
    have hnat : (5265107867 : ℕ)^4193*20000000000000^3169 ≤ 8558851876231^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265107867 10000000000 8558851876231 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103893909/5000000000 : ℝ)^4193 ≤ (13550959658289/100000000000000 : ℝ)^3169 := by
    have hnat : (1103893909 : ℕ)^4193*100000000000000^3169 ≤ 13550959658289^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103893909 5000000000 13550959658289 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672464881/5000000000 : ℝ), (5265107867/10000000000 : ℝ), (-1103893909/5000000000 : ℝ)] ![(4365478094689/10000000000000 : ℝ), (8558851876231/20000000000000 : ℝ), (13550959658289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672464881/5000000000 : ℝ)|^4193 ≤ (4365478094689/10000000000000 : ℝ)^3169
        have hw : |(2672464881/5000000000 : ℝ)|=(2672464881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265107867/10000000000 : ℝ)|^4193 ≤ (8558851876231/20000000000000 : ℝ)^3169
        have hw : |(5265107867/10000000000 : ℝ)|=(5265107867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103893909/5000000000 : ℝ)|^4193 ≤ (13550959658289/100000000000000 : ℝ)^3169
        have hw : |(-1103893909/5000000000 : ℝ)|=(1103893909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178731297/5000000000 : ℝ)*x 0 + (846047407/2000000000 : ℝ)*x 1 + (4488449551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178731297/5000000000 : ℝ)^4193 ≤ (16658240574291/50000000000000 : ℝ)^3169 := by
    have hnat : (2178731297 : ℕ)^4193*50000000000000^3169 ≤ 16658240574291^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178731297 5000000000 16658240574291 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846047407/2000000000 : ℝ)^4193 ≤ (32035522236857/100000000000000 : ℝ)^3169 := by
    have hnat : (846047407 : ℕ)^4193*100000000000000^3169 ≤ 32035522236857^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846047407 2000000000 32035522236857 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488449551/10000000000 : ℝ)^4193 ≤ (4330999574997/12500000000000 : ℝ)^3169 := by
    have hnat : (4488449551 : ℕ)^4193*12500000000000^3169 ≤ 4330999574997^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488449551 10000000000 4330999574997 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178731297/5000000000 : ℝ), (846047407/2000000000 : ℝ), (4488449551/10000000000 : ℝ)] ![(16658240574291/50000000000000 : ℝ), (32035522236857/100000000000000 : ℝ), (4330999574997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178731297/5000000000 : ℝ)|^4193 ≤ (16658240574291/50000000000000 : ℝ)^3169
        have hw : |(2178731297/5000000000 : ℝ)|=(2178731297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846047407/2000000000 : ℝ)|^4193 ≤ (32035522236857/100000000000000 : ℝ)^3169
        have hw : |(846047407/2000000000 : ℝ)|=(846047407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488449551/10000000000 : ℝ)|^4193 ≤ (4330999574997/12500000000000 : ℝ)^3169
        have hw : |(4488449551/10000000000 : ℝ)|=(4488449551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142605667/10000000000 : ℝ)*x 0 + (2632719419/5000000000 : ℝ)*x 1 + (5393278349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142605667/10000000000 : ℝ)^4193 ≤ (13024150342343/100000000000000 : ℝ)^3169 := by
    have hnat : (2142605667 : ℕ)^4193*100000000000000^3169 ≤ 13024150342343^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142605667 10000000000 13024150342343 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632719419/5000000000 : ℝ)^4193 ≤ (21398909384109/50000000000000 : ℝ)^3169 := by
    have hnat : (2632719419 : ℕ)^4193*50000000000000^3169 ≤ 21398909384109^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632719419 5000000000 21398909384109 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393278349/10000000000 : ℝ)^4193 ≤ (44178030873497/100000000000000 : ℝ)^3169 := by
    have hnat : (5393278349 : ℕ)^4193*100000000000000^3169 ≤ 44178030873497^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393278349 10000000000 44178030873497 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142605667/10000000000 : ℝ), (2632719419/5000000000 : ℝ), (5393278349/10000000000 : ℝ)] ![(13024150342343/100000000000000 : ℝ), (21398909384109/50000000000000 : ℝ), (44178030873497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142605667/10000000000 : ℝ)|^4193 ≤ (13024150342343/100000000000000 : ℝ)^3169
        have hw : |(-2142605667/10000000000 : ℝ)|=(2142605667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632719419/5000000000 : ℝ)|^4193 ≤ (21398909384109/50000000000000 : ℝ)^3169
        have hw : |(2632719419/5000000000 : ℝ)|=(2632719419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393278349/10000000000 : ℝ)|^4193 ≤ (44178030873497/100000000000000 : ℝ)^3169
        have hw : |(5393278349/10000000000 : ℝ)|=(5393278349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656126449/5000000000 : ℝ)*x 0 + (-1039808673/5000000000 : ℝ)*x 1 + (1348319589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656126449/5000000000 : ℝ)^4193 ≤ (21651000851369/50000000000000 : ℝ)^3169 := by
    have hnat : (2656126449 : ℕ)^4193*50000000000000^3169 ≤ 21651000851369^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656126449 5000000000 21651000851369 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039808673/5000000000 : ℝ)^4193 ≤ (12519967331421/100000000000000 : ℝ)^3169 := by
    have hnat : (1039808673 : ℕ)^4193*100000000000000^3169 ≤ 12519967331421^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039808673 5000000000 12519967331421 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348319589/2500000000 : ℝ)^4193 ≤ (11044507737341/25000000000000 : ℝ)^3169 := by
    have hnat : (1348319589 : ℕ)^4193*25000000000000^3169 ≤ 11044507737341^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348319589 2500000000 11044507737341 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656126449/5000000000 : ℝ), (-1039808673/5000000000 : ℝ), (1348319589/2500000000 : ℝ)] ![(21651000851369/50000000000000 : ℝ), (12519967331421/100000000000000 : ℝ), (11044507737341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656126449/5000000000 : ℝ)|^4193 ≤ (21651000851369/50000000000000 : ℝ)^3169
        have hw : |(2656126449/5000000000 : ℝ)|=(2656126449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039808673/5000000000 : ℝ)|^4193 ≤ (12519967331421/100000000000000 : ℝ)^3169
        have hw : |(-1039808673/5000000000 : ℝ)|=(1039808673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348319589/2500000000 : ℝ)|^4193 ≤ (11044507737341/25000000000000 : ℝ)^3169
        have hw : |(1348319589/2500000000 : ℝ)|=(1348319589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328063223/2500000000 : ℝ)*x 0 + (5393278361/10000000000 : ℝ)*x 1 + (-2079617347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328063223/2500000000 : ℝ)^4193 ≤ (21651000819013/50000000000000 : ℝ)^3169 := by
    have hnat : (1328063223 : ℕ)^4193*50000000000000^3169 ≤ 21651000819013^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328063223 2500000000 21651000819013 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393278361/10000000000 : ℝ)^4193 ≤ (8835606200711/20000000000000 : ℝ)^3169 := by
    have hnat : (5393278361 : ℕ)^4193*20000000000000^3169 ≤ 8835606200711^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393278361 10000000000 8835606200711 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079617347/10000000000 : ℝ)^4193 ≤ (12519967339387/100000000000000 : ℝ)^3169 := by
    have hnat : (2079617347 : ℕ)^4193*100000000000000^3169 ≤ 12519967339387^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079617347 10000000000 12519967339387 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328063223/2500000000 : ℝ), (5393278361/10000000000 : ℝ), (-2079617347/10000000000 : ℝ)] ![(21651000819013/50000000000000 : ℝ), (8835606200711/20000000000000 : ℝ), (12519967339387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328063223/2500000000 : ℝ)|^4193 ≤ (21651000819013/50000000000000 : ℝ)^3169
        have hw : |(1328063223/2500000000 : ℝ)|=(1328063223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393278361/10000000000 : ℝ)|^4193 ≤ (8835606200711/20000000000000 : ℝ)^3169
        have hw : |(5393278361/10000000000 : ℝ)|=(5393278361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079617347/10000000000 : ℝ)|^4193 ≤ (12519967339387/100000000000000 : ℝ)^3169
        have hw : |(-2079617347/10000000000 : ℝ)|=(2079617347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s5_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871494577/2000000000 : ℝ)*x 0 + (1121946133/2500000000 : ℝ)*x 1 + (2115452243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871494577/2000000000 : ℝ)^4193 ≤ (6663317051399/20000000000000 : ℝ)^3169 := by
    have hnat : (871494577 : ℕ)^4193*20000000000000^3169 ≤ 6663317051399^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871494577 2000000000 6663317051399 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121946133/2500000000 : ℝ)^4193 ≤ (17320602218797/50000000000000 : ℝ)^3169 := by
    have hnat : (1121946133 : ℕ)^4193*50000000000000^3169 ≤ 17320602218797^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121946133 2500000000 17320602218797 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115452243/5000000000 : ℝ)^4193 ≤ (32042210297261/100000000000000 : ℝ)^3169 := by
    have hnat : (2115452243 : ℕ)^4193*100000000000000^3169 ≤ 32042210297261^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115452243 5000000000 32042210297261 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871494577/2000000000 : ℝ), (1121946133/2500000000 : ℝ), (2115452243/5000000000 : ℝ)] ![(6663317051399/20000000000000 : ℝ), (17320602218797/50000000000000 : ℝ), (32042210297261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871494577/2000000000 : ℝ)|^4193 ≤ (6663317051399/20000000000000 : ℝ)^3169
        have hw : |(871494577/2000000000 : ℝ)|=(871494577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121946133/2500000000 : ℝ)|^4193 ≤ (17320602218797/50000000000000 : ℝ)^3169
        have hw : |(1121946133/2500000000 : ℝ)|=(1121946133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115452243/5000000000 : ℝ)|^4193 ≤ (32042210297261/100000000000000 : ℝ)^3169
        have hw : |(2115452243/5000000000 : ℝ)|=(2115452243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2847/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1411/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (13127826345187081/100000000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^8385 ≤ (13127826345187081/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11269 : ℕ)^8385*100000000000000000000^2048 ≤ 13127826345187081^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 13127826345187081 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (13127826345187081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8385/2048 : ℝ) ≤ (6833980651403147/20000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8385 ≤ (6833980651403147/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8385*20000000000000000000^2048 ≤ 6833980651403147^2048*20000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 6833980651403147 20000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (6833980651403147/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013127826345187081/50000000000000000000 : ℝ) ≤ (5000320609675791/5000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50013127826345187081/50000000000000000000 : ℝ)^2048 ≤ (5000320609675791/5000000000000000 : ℝ)^8385 := by
      have hnat : (50013127826345187081 : ℕ)^2048*5000000000000000^8385 ≤ 5000320609675791^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013127826345187081 50000000000000000000 5000320609675791 5000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000320609675791/5000000000000000 : ℝ)) (X := (50013127826345187081/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563239027025034419/1562500000000000000 : ℝ) ≤ (10001155020184381/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (1563239027025034419/1562500000000000000 : ℝ)^2048 ≤ (10001155020184381/10000000000000000 : ℝ)^8385 := by
      have hnat : (1563239027025034419 : ℕ)^2048*10000000000000000^8385 ≤ 10001155020184381^8385*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563239027025034419 1562500000000000000 10001155020184381 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001155020184381/10000000000000000 : ℝ)) (X := (1563239027025034419/1562500000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006833980651403147/10000000000000000000 : ℝ) ≤ (500083441050859/500000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (10006833980651403147/10000000000000000000 : ℝ)^2048 ≤ (500083441050859/500000000000000 : ℝ)^8385 := by
      have hnat : (10006833980651403147 : ℕ)^2048*500000000000000^8385 ≤ 500083441050859^8385*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006833980651403147 10000000000000000000 500083441050859 500000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500083441050859/500000000000000 : ℝ)) (X := (10006833980651403147/10000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13127826345187081/100000000000000000000 : ℝ) ≤ ((593006436268543367/593200000000000000 : ℝ)+2*(513800832799/296600000000000 : ℝ)*(11269/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (593006436268543367/593200000000000000 : ℝ)+2*(513800832799/296600000000000 : ℝ)*(11269/100000 : ℝ)=(5000320609675791/5000000000000000 : ℝ) by norm_num, show 1+2*(13127826345187081/100000000000000000000 : ℝ)=(50013127826345187081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6833980651403147/20000000000000000000 : ℝ)+(13127826345187081/100000000000000000000 : ℝ) ≤ ((593006436268543367/593200000000000000 : ℝ)+(513800832799/296600000000000 : ℝ)*((2847/20000 : ℝ)+(11269/100000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (593006436268543367/593200000000000000 : ℝ)+(513800832799/296600000000000 : ℝ)*((2847/20000 : ℝ)+(11269/100000 : ℝ))=(10001155020184381/10000000000000000 : ℝ) by norm_num, show 1+(6833980651403147/20000000000000000000 : ℝ)+(13127826345187081/100000000000000000000 : ℝ)=(1563239027025034419/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6833980651403147/20000000000000000000 : ℝ) ≤ ((593006436268543367/593200000000000000 : ℝ)+2*(513800832799/296600000000000 : ℝ)*(2847/20000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (593006436268543367/593200000000000000 : ℝ)+2*(513800832799/296600000000000 : ℝ)*(2847/20000 : ℝ)=(500083441050859/500000000000000 : ℝ) by norm_num, show 1+2*(6833980651403147/20000000000000000000 : ℝ)=(10006833980651403147/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (593006436268543367/593200000000000000 : ℝ)*(X 1 0+X 2 0)+(513800832799/296600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (593006436268543367/593200000000000000 : ℝ)) (alpha := (513800832799/296600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (593006436268543367/593200000000000000 : ℝ)*(X 0 1+X 2 1)+(513800832799/296600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (593006436268543367/593200000000000000 : ℝ)) (alpha := (513800832799/296600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (593006436268543367/593200000000000000 : ℝ)*(X 0 2+X 1 2)+(513800832799/296600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (593006436268543367/593200000000000000 : ℝ)) (alpha := (513800832799/296600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-535650141/2500000000 : ℝ)*X 0 0+(337100657/625000000 : ℝ)*X 0 1+(52651079/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068985943/2000000000 : ℝ)*X 1 0+(-551946961/2500000000 : ℝ)*X 1 1+(1053021579/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672464881/5000000000 : ℝ)*X 2 0+(5265107867/10000000000 : ℝ)*X 2 1+(-1103893909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178731297/5000000000 : ℝ)*X 0 0+(846047407/2000000000 : ℝ)*X 0 1+(4488449551/10000000000 : ℝ)*X 0 2+(2178731297/5000000000 : ℝ)*X 1 0+(846047407/2000000000 : ℝ)*X 1 1+(4488449551/10000000000 : ℝ)*X 1 2+(2178731297/5000000000 : ℝ)*X 2 0+(846047407/2000000000 : ℝ)*X 2 1+(4488449551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2142605667/10000000000 : ℝ)*X 0 0+(2632719419/5000000000 : ℝ)*X 0 1+(5393278349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656126449/5000000000 : ℝ)*X 1 0+(-1039808673/5000000000 : ℝ)*X 1 1+(1348319589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328063223/2500000000 : ℝ)*X 2 0+(5393278361/10000000000 : ℝ)*X 2 1+(-2079617347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871494577/2000000000 : ℝ)*X 0 0+(1121946133/2500000000 : ℝ)*X 0 1+(2115452243/5000000000 : ℝ)*X 0 2+(871494577/2000000000 : ℝ)*X 1 0+(1121946133/2500000000 : ℝ)*X 1 1+(2115452243/5000000000 : ℝ)*X 1 2+(871494577/2000000000 : ℝ)*X 2 0+(1121946133/2500000000 : ℝ)*X 2 1+(2115452243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40817107215162751039230711/7415000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (959254459/100000000000000 : ℝ)*(base19) + (15348927/1562500000000 : ℝ)*(base23) + (484819/2000000000000 : ℝ)*(lower2) + (48140093/50000000000000 : ℝ)*(upper3) + (116331311/100000000000000 : ℝ)*(upper5) + (1456850166211611/25000000000000 : ℝ)*(major0) + (1456850166211611/25000000000000 : ℝ)*(major1) + (1456850166211611/25000000000000 : ℝ)*(major2) + (7781968058150507/100000000000000 : ℝ)*(sp0) + (7781994720352741/100000000000000 : ℝ)*(sp1) + (7781994697275871/100000000000000 : ℝ)*(sp2) + (1936396039086069/50000000000000 : ℝ)*(sp3) + (6905364173/25000000000000 : ℝ)*(sp4) + (2677684927/20000000000000 : ℝ)*(sp7) + (1936402733298387/50000000000000 : ℝ)*(f.failure) + (7781995679607199/100000000000000 : ℝ)*(f.sum) + (26953777087147/7415000000000000000000000000 : ℝ)*base66 + (214123590282912237/14830000000000000000000000000000 : ℝ)*base67 + (21815471121667763/14830000000000000000000000000000 : ℝ)*base70 + (21325151369647763/14830000000000000000000000000000 : ℝ)*base72 + (1946686918393/463437500000000000000000000 : ℝ)*base73 + (395895152950877763/14830000000000000000000000000000 : ℝ)*base76 + (59583198113857763/14830000000000000000000000000000 : ℝ)*base78 + (38443796553002237/14830000000000000000000000000000 : ℝ)*base79 + (2446854961793/1853750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (33994863/5000000000000000000000 : ℝ)*base89 + (33994863/5000000000000000000000 : ℝ)*base91 + (33994863/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14352235507105231144361169/1853750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (691269323/50000000000000 : ℝ)*(base19) + (745377549/50000000000000 : ℝ)*(base23) + (75854067/50000000000000 : ℝ)*(upper3) + (13642563/25000000000000 : ℝ)*(lower4) + (162943859/100000000000000 : ℝ)*(upper5) + (366099182788423/6250000000000 : ℝ)*(major0) + (366099182788423/6250000000000 : ℝ)*(major1) + (366099182788423/6250000000000 : ℝ)*(major2) + (9570546643/25000000000000 : ℝ)*(sp1) + (20305562763/50000000000000 : ℝ)*(sp2) + (3911153388349397/50000000000000 : ℝ)*(sp4) + (312890684478943/4000000000000 : ℝ)*(sp5) + (782226467481817/10000000000000 : ℝ)*(sp6) + (1946433407227511/50000000000000 : ℝ)*(sp7) + (1946433407227511/50000000000000 : ℝ)*(f.failure) + (3911153388349397/50000000000000 : ℝ)*(f.sum) + (1457636415121/463437500000000000000000000 : ℝ)*base65 + (32712816256275759/3707500000000000000000000000000 : ℝ)*base68 + (6553655468090759/3707500000000000000000000000000 : ℝ)*base70 + (18696073895505759/3707500000000000000000000000000 : ℝ)*base72 + (9305182268313/3707500000000000000000000000 : ℝ)*base73 + (25895747975395759/3707500000000000000000000000000 : ℝ)*base76 + (8470770810320759/3707500000000000000000000000000 : ℝ)*base78 + (29681456887075759/3707500000000000000000000000000 : ℝ)*base80 + (8396404197647/3707500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (33935261/5000000000000000000000 : ℝ)*base90 + (33935261/5000000000000000000000 : ℝ)*base92 + (33935261/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1193_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1193_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1193_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1193_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1193_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
