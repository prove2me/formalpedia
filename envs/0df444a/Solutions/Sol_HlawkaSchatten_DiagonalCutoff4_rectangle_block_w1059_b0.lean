-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1059_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:01:51.390207+00:00
-- url     : https://prove2.me/submissions/d8a02fc3-0bfa-4960-ad06-aded9fd92537

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
theorem support_rectangle_w1059_s0_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1918360633/10000000000 : ℝ)*x 0 + (6073713143/10000000000 : ℝ)*x 1 + (4769886171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1918360633/10000000000 : ℝ)^2063 ≤ (11122915595469/100000000000000 : ℝ)^1551 := by
    have hnat : (1918360633 : ℕ)^2063*100000000000000^1551 ≤ 11122915595469^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918360633 10000000000 11122915595469 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6073713143/10000000000 : ℝ)^2063 ≤ (12879839814231/25000000000000 : ℝ)^1551 := by
    have hnat : (6073713143 : ℕ)^2063*25000000000000^1551 ≤ 12879839814231^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6073713143 10000000000 12879839814231 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4769886171/10000000000 : ℝ)^2063 ≤ (18678862569257/50000000000000 : ℝ)^1551 := by
    have hnat : (4769886171 : ℕ)^2063*50000000000000^1551 ≤ 18678862569257^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4769886171 10000000000 18678862569257 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1918360633/10000000000 : ℝ), (6073713143/10000000000 : ℝ), (4769886171/10000000000 : ℝ)] ![(11122915595469/100000000000000 : ℝ), (12879839814231/25000000000000 : ℝ), (18678862569257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1918360633/10000000000 : ℝ)|^2063 ≤ (11122915595469/100000000000000 : ℝ)^1551
        have hw : |(-1918360633/10000000000 : ℝ)|=(1918360633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6073713143/10000000000 : ℝ)|^2063 ≤ (12879839814231/25000000000000 : ℝ)^1551
        have hw : |(6073713143/10000000000 : ℝ)|=(6073713143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4769886171/10000000000 : ℝ)|^2063 ≤ (18678862569257/50000000000000 : ℝ)^1551
        have hw : |(4769886171/10000000000 : ℝ)|=(4769886171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (69018333/125000000 : ℝ)*x 0 + (-2669059863/10000000000 : ℝ)*x 1 + (953977289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69018333/125000000 : ℝ)^2063 ≤ (4538414408389/10000000000000 : ℝ)^1551 := by
    have hnat : (69018333 : ℕ)^2063*10000000000000^1551 ≤ 4538414408389^1551*125000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69018333 125000000 4538414408389 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2669059863/10000000000 : ℝ)^2063 ≤ (862906395093/5000000000000 : ℝ)^1551 := by
    have hnat : (2669059863 : ℕ)^2063*5000000000000^1551 ≤ 862906395093^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669059863 10000000000 862906395093 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953977289/2000000000 : ℝ)^2063 ≤ (7471545598577/20000000000000 : ℝ)^1551 := by
    have hnat : (953977289 : ℕ)^2063*20000000000000^1551 ≤ 7471545598577^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953977289 2000000000 7471545598577 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(69018333/125000000 : ℝ), (-2669059863/10000000000 : ℝ), (953977289/2000000000 : ℝ)] ![(4538414408389/10000000000000 : ℝ), (862906395093/5000000000000 : ℝ), (7471545598577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(69018333/125000000 : ℝ)|^2063 ≤ (4538414408389/10000000000000 : ℝ)^1551
        have hw : |(69018333/125000000 : ℝ)|=(69018333/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2669059863/10000000000 : ℝ)|^2063 ≤ (862906395093/5000000000000 : ℝ)^1551
        have hw : |(-2669059863/10000000000 : ℝ)|=(2669059863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(953977289/2000000000 : ℝ)|^2063 ≤ (7471545598577/20000000000000 : ℝ)^1551
        have hw : |(953977289/2000000000 : ℝ)|=(953977289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2760733467/5000000000 : ℝ)*x 0 + (38159091/80000000 : ℝ)*x 1 + (-106762383/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760733467/5000000000 : ℝ)^2063 ≤ (354563650767/781250000000 : ℝ)^1551 := by
    have hnat : (2760733467 : ℕ)^2063*781250000000^1551 ≤ 354563650767^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760733467 5000000000 354563650767 781250000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38159091/80000000 : ℝ)^2063 ≤ (18678863631833/50000000000000 : ℝ)^1551 := by
    have hnat : (38159091 : ℕ)^2063*50000000000000^1551 ≤ 18678863631833^1551*80000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38159091 80000000 18678863631833 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106762383/400000000 : ℝ)^2063 ≤ (17258125424921/100000000000000 : ℝ)^1551 := by
    have hnat : (106762383 : ℕ)^2063*100000000000000^1551 ≤ 17258125424921^1551*400000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106762383 400000000 17258125424921 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760733467/5000000000 : ℝ), (38159091/80000000 : ℝ), (-106762383/400000000 : ℝ)] ![(354563650767/781250000000 : ℝ), (18678863631833/50000000000000 : ℝ), (17258125424921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760733467/5000000000 : ℝ)|^2063 ≤ (354563650767/781250000000 : ℝ)^1551
        have hw : |(2760733467/5000000000 : ℝ)|=(2760733467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38159091/80000000 : ℝ)|^2063 ≤ (18678863631833/50000000000000 : ℝ)^1551
        have hw : |(38159091/80000000 : ℝ)|=(38159091/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106762383/400000000 : ℝ)|^2063 ≤ (17258125424921/100000000000000 : ℝ)^1551
        have hw : |(-106762383/400000000 : ℝ)|=(106762383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4207789551/10000000000 : ℝ)*x 0 + (3125242823/10000000000 : ℝ)*x 1 + (283850569/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207789551/10000000000 : ℝ)^2063 ≤ (31619181840509/100000000000000 : ℝ)^1551 := by
    have hnat : (4207789551 : ℕ)^2063*100000000000000^1551 ≤ 31619181840509^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207789551 10000000000 31619181840509 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3125242823/10000000000 : ℝ)^2063 ≤ (21288254097499/100000000000000 : ℝ)^1551 := by
    have hnat : (3125242823 : ℕ)^2063*100000000000000^1551 ≤ 21288254097499^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125242823 10000000000 21288254097499 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283850569/500000000 : ℝ)^2063 ≤ (47092564043059/100000000000000 : ℝ)^1551 := by
    have hnat : (283850569 : ℕ)^2063*100000000000000^1551 ≤ 47092564043059^1551*500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283850569 500000000 47092564043059 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207789551/10000000000 : ℝ), (3125242823/10000000000 : ℝ), (283850569/500000000 : ℝ)] ![(31619181840509/100000000000000 : ℝ), (21288254097499/100000000000000 : ℝ), (47092564043059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207789551/10000000000 : ℝ)|^2063 ≤ (31619181840509/100000000000000 : ℝ)^1551
        have hw : |(4207789551/10000000000 : ℝ)|=(4207789551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3125242823/10000000000 : ℝ)|^2063 ≤ (21288254097499/100000000000000 : ℝ)^1551
        have hw : |(3125242823/10000000000 : ℝ)|=(3125242823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283850569/500000000 : ℝ)|^2063 ≤ (47092564043059/100000000000000 : ℝ)^1551
        have hw : |(283850569/500000000 : ℝ)|=(283850569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1923754851/10000000000 : ℝ)*x 0 + (4803554219/10000000000 : ℝ)*x 1 + (6038868333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1923754851/10000000000 : ℝ)^2063 ≤ (11164535942969/100000000000000 : ℝ)^1551 := by
    have hnat : (1923754851 : ℕ)^2063*100000000000000^1551 ≤ 11164535942969^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923754851 10000000000 11164535942969 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4803554219/10000000000 : ℝ)^2063 ≤ (7541773407531/20000000000000 : ℝ)^1551 := by
    have hnat : (4803554219 : ℕ)^2063*20000000000000^1551 ≤ 7541773407531^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803554219 10000000000 7541773407531 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6038868333/10000000000 : ℝ)^2063 ≤ (5112659700353/10000000000000 : ℝ)^1551 := by
    have hnat : (6038868333 : ℕ)^2063*10000000000000^1551 ≤ 5112659700353^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038868333 10000000000 5112659700353 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1923754851/10000000000 : ℝ), (4803554219/10000000000 : ℝ), (6038868333/10000000000 : ℝ)] ![(11164535942969/100000000000000 : ℝ), (7541773407531/20000000000000 : ℝ), (5112659700353/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1923754851/10000000000 : ℝ)|^2063 ≤ (11164535942969/100000000000000 : ℝ)^1551
        have hw : |(-1923754851/10000000000 : ℝ)|=(1923754851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4803554219/10000000000 : ℝ)|^2063 ≤ (7541773407531/20000000000000 : ℝ)^1551
        have hw : |(4803554219/10000000000 : ℝ)|=(4803554219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6038868333/10000000000 : ℝ)|^2063 ≤ (5112659700353/10000000000000 : ℝ)^1551
        have hw : |(6038868333/10000000000 : ℝ)|=(6038868333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (516762597/1000000000 : ℝ)*x 0 + (-1400081171/10000000000 : ℝ)*x 1 + (1509716649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516762597/1000000000 : ℝ)^2063 ≤ (41557144720131/100000000000000 : ℝ)^1551 := by
    have hnat : (516762597 : ℕ)^2063*100000000000000^1551 ≤ 41557144720131^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516762597 1000000000 41557144720131 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400081171/10000000000 : ℝ)^2063 ≤ (7316277822331/100000000000000 : ℝ)^1551 := by
    have hnat : (1400081171 : ℕ)^2063*100000000000000^1551 ≤ 7316277822331^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400081171 10000000000 7316277822331 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1509716649/2500000000 : ℝ)^2063 ≤ (51126577443093/100000000000000 : ℝ)^1551 := by
    have hnat : (1509716649 : ℕ)^2063*100000000000000^1551 ≤ 51126577443093^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509716649 2500000000 51126577443093 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516762597/1000000000 : ℝ), (-1400081171/10000000000 : ℝ), (1509716649/2500000000 : ℝ)] ![(41557144720131/100000000000000 : ℝ), (7316277822331/100000000000000 : ℝ), (51126577443093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516762597/1000000000 : ℝ)|^2063 ≤ (41557144720131/100000000000000 : ℝ)^1551
        have hw : |(516762597/1000000000 : ℝ)|=(516762597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1400081171/10000000000 : ℝ)|^2063 ≤ (7316277822331/100000000000000 : ℝ)^1551
        have hw : |(-1400081171/10000000000 : ℝ)|=(1400081171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1509716649/2500000000 : ℝ)|^2063 ≤ (51126577443093/100000000000000 : ℝ)^1551
        have hw : |(1509716649/2500000000 : ℝ)|=(1509716649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2583813457/5000000000 : ℝ)*x 0 + (6038866773/10000000000 : ℝ)*x 1 + (-175009929/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583813457/5000000000 : ℝ)^2063 ≤ (10389288704409/25000000000000 : ℝ)^1551 := by
    have hnat : (2583813457 : ℕ)^2063*25000000000000^1551 ≤ 10389288704409^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583813457 5000000000 10389288704409 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6038866773/10000000000 : ℝ)^2063 ≤ (25563289718149/50000000000000 : ℝ)^1551 := by
    have hnat : (6038866773 : ℕ)^2063*50000000000000^1551 ≤ 25563289718149^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038866773 10000000000 25563289718149 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175009929/1250000000 : ℝ)^2063 ≤ (7316265735181/100000000000000 : ℝ)^1551 := by
    have hnat : (175009929 : ℕ)^2063*100000000000000^1551 ≤ 7316265735181^1551*1250000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175009929 1250000000 7316265735181 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583813457/5000000000 : ℝ), (6038866773/10000000000 : ℝ), (-175009929/1250000000 : ℝ)] ![(10389288704409/25000000000000 : ℝ), (25563289718149/50000000000000 : ℝ), (7316265735181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583813457/5000000000 : ℝ)|^2063 ≤ (10389288704409/25000000000000 : ℝ)^1551
        have hw : |(2583813457/5000000000 : ℝ)|=(2583813457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6038866773/10000000000 : ℝ)|^2063 ≤ (25563289718149/50000000000000 : ℝ)^1551
        have hw : |(6038866773/10000000000 : ℝ)|=(6038866773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175009929/1250000000 : ℝ)|^2063 ≤ (7316265735181/100000000000000 : ℝ)^1551
        have hw : |(-175009929/1250000000 : ℝ)|=(175009929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s0_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4218347241/10000000000 : ℝ)*x 0 + (224444631/400000000 : ℝ)*x 1 + (3193440271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4218347241/10000000000 : ℝ)^2063 ≤ (6344949986513/20000000000000 : ℝ)^1551 := by
    have hnat : (4218347241 : ℕ)^2063*20000000000000^1551 ≤ 6344949986513^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218347241 10000000000 6344949986513 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224444631/400000000 : ℝ)^2063 ≤ (23183445130029/50000000000000 : ℝ)^1551 := by
    have hnat : (224444631 : ℕ)^2063*50000000000000^1551 ≤ 23183445130029^1551*400000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224444631 400000000 23183445130029 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193440271/10000000000 : ℝ)^2063 ≤ (4381671956327/20000000000000 : ℝ)^1551 := by
    have hnat : (3193440271 : ℕ)^2063*20000000000000^1551 ≤ 4381671956327^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193440271 10000000000 4381671956327 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4218347241/10000000000 : ℝ), (224444631/400000000 : ℝ), (3193440271/10000000000 : ℝ)] ![(6344949986513/20000000000000 : ℝ), (23183445130029/50000000000000 : ℝ), (4381671956327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4218347241/10000000000 : ℝ)|^2063 ≤ (6344949986513/20000000000000 : ℝ)^1551
        have hw : |(4218347241/10000000000 : ℝ)|=(4218347241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224444631/400000000 : ℝ)|^2063 ≤ (23183445130029/50000000000000 : ℝ)^1551
        have hw : |(224444631/400000000 : ℝ)|=(224444631/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193440271/10000000000 : ℝ)|^2063 ≤ (4381671956327/20000000000000 : ℝ)^1551
        have hw : |(3193440271/10000000000 : ℝ)|=(3193440271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (67/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/12500 : ℝ)*pair X 0 0 := by
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
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
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
  have hpowlo : (0 : ℝ) ^ (8251/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8251 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8251*1^2048 ≤ 0^2048*1^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8251/2048 : ℝ) ≤ (1246653835692468719/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8251 ≤ (1246653835692468719/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8251*50000000000000000000^2048 ≤ 1246653835692468719^2048*5^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1246653835692468719 50000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1246653835692468719/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8251 := by
      have hnat : (1 : ℕ)^2048*1^8251 ≤ 1^8251*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51246653835692468719/50000000000000000000 : ℝ) ≤ (2515328814632847/2500000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (51246653835692468719/50000000000000000000 : ℝ)^2048 ≤ (2515328814632847/2500000000000000 : ℝ)^8251 := by
      have hnat : (51246653835692468719 : ℕ)^2048*2500000000000000^8251 ≤ 2515328814632847^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51246653835692468719 50000000000000000000 2515328814632847 2500000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515328814632847/2500000000000000 : ℝ)) (X := (51246653835692468719/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26246653835692468719/25000000000000000000 : ℝ) ≤ (1265328814632847/1250000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (26246653835692468719/25000000000000000000 : ℝ)^2048 ≤ (1265328814632847/1250000000000000 : ℝ)^8251 := by
      have hnat : (26246653835692468719 : ℕ)^2048*1250000000000000^8251 ≤ 1265328814632847^8251*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26246653835692468719 25000000000000000000 1265328814632847 1250000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265328814632847/1250000000000000 : ℝ)) (X := (26246653835692468719/25000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15328814632847/1000000000000000 : ℝ)*(0 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15328814632847/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1246653835692468719/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15328814632847/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (1 : ℝ)+(15328814632847/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515328814632847/2500000000000000 : ℝ) by norm_num, show 1+(1246653835692468719/50000000000000000000 : ℝ)+(0 : ℝ)=(51246653835692468719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1246653835692468719/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15328814632847/1000000000000000 : ℝ)*(2/5 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15328814632847/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265328814632847/1250000000000000 : ℝ) by norm_num, show 1+2*(1246653835692468719/50000000000000000000 : ℝ)=(26246653835692468719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15328814632847/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15328814632847/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15328814632847/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15328814632847/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15328814632847/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15328814632847/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1918360633/10000000000 : ℝ)*X 0 0+(6073713143/10000000000 : ℝ)*X 0 1+(4769886171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((69018333/125000000 : ℝ)*X 1 0+(-2669059863/10000000000 : ℝ)*X 1 1+(953977289/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2760733467/5000000000 : ℝ)*X 2 0+(38159091/80000000 : ℝ)*X 2 1+(-106762383/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4207789551/10000000000 : ℝ)*X 0 0+(3125242823/10000000000 : ℝ)*X 0 1+(283850569/500000000 : ℝ)*X 0 2+(4207789551/10000000000 : ℝ)*X 1 0+(3125242823/10000000000 : ℝ)*X 1 1+(283850569/500000000 : ℝ)*X 1 2+(4207789551/10000000000 : ℝ)*X 2 0+(3125242823/10000000000 : ℝ)*X 2 1+(283850569/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1923754851/10000000000 : ℝ)*X 0 0+(4803554219/10000000000 : ℝ)*X 0 1+(6038868333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516762597/1000000000 : ℝ)*X 1 0+(-1400081171/10000000000 : ℝ)*X 1 1+(1509716649/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583813457/5000000000 : ℝ)*X 2 0+(6038866773/10000000000 : ℝ)*X 2 1+(-175009929/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4218347241/10000000000 : ℝ)*X 0 0+(224444631/400000000 : ℝ)*X 0 1+(3193440271/10000000000 : ℝ)*X 0 2+(4218347241/10000000000 : ℝ)*X 1 0+(224444631/400000000 : ℝ)*X 1 1+(3193440271/10000000000 : ℝ)*X 1 2+(4218347241/10000000000 : ℝ)*X 2 0+(224444631/400000000 : ℝ)*X 2 1+(3193440271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3883132502019076473/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13506267/100000000000000 : ℝ)*(base1) + (914127003/100000000000000 : ℝ)*(base19) + (431267017/50000000000000 : ℝ)*(base23) + (92431991/100000000000000 : ℝ)*(base24) + (113237023/50000000000000 : ℝ)*(upper3) + (72429127753989/12500000000000 : ℝ)*(major0) + (72429127753989/12500000000000 : ℝ)*(major1) + (72429127753989/12500000000000 : ℝ)*(major2) + (766976073627943/100000000000000 : ℝ)*(sp0) + (4793607773251/625000000000 : ℝ)*(sp1) + (766977202881137/100000000000000 : ℝ)*(sp2) + (195943017268257/50000000000000 : ℝ)*(sp3) + (2097725487/100000000000000 : ℝ)*(sp4) + (13669889/800000000000 : ℝ)*(sp7) + (195943878389453/50000000000000 : ℝ)*(f.failure) + (383489078923581/50000000000000 : ℝ)*(f.sum) + (2567081032933/6250000000000000000000000000 : ℝ)*base65 + (49694792810817/12500000000000000000000000000 : ℝ)*base68 + (4135791939183/12500000000000000000000000000 : ℝ)*base69 + (60691834560817/12500000000000000000000000000 : ℝ)*base72 + (10414069570433/6250000000000000000000000000 : ℝ)*base73 + (54252355260817/12500000000000000000000000000 : ℝ)*base76 + (7528645964183/12500000000000000000000000000 : ℝ)*base77 + (45281966223317/12500000000000000000000000000 : ℝ)*base80 + (1113490448317/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (19345001/5000000000000000000000 : ℝ)*base90 + (19345001/5000000000000000000000 : ℝ)*base92 + (19345001/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10565048299230262097421/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50744267/20000000000000 : ℝ)*(base19) + (207148953/50000000000000 : ℝ)*(base23) + (5804327/50000000000000 : ℝ)*(base51) + (92383231/50000000000000 : ℝ)*(upper5) + (305783395779569/50000000000000 : ℝ)*(major0) + (305783395779569/50000000000000 : ℝ)*(major1) + (305783395779569/50000000000000 : ℝ)*(major2) + (316079767/100000000000000 : ℝ)*(sp0) + (51352741/10000000000000 : ℝ)*(sp2) + (340594531/100000000000000 : ℝ)*(sp3) + (404756215747919/50000000000000 : ℝ)*(sp4) + (809512493854269/100000000000000 : ℝ)*(sp5) + (809511819750289/100000000000000 : ℝ)*(sp6) + (103405109650303/25000000000000 : ℝ)*(sp7) + (413620779195743/100000000000000 : ℝ)*(f.failure) + (161902549515121/20000000000000 : ℝ)*(f.sum) + (108630603302943/25000000000000000000000000000 : ℝ)*base65 + (36958153102943/50000000000000000000000000000 : ℝ)*base67 + (58563493247057/50000000000000000000000000000 : ℝ)*base70 + (148431698752943/50000000000000000000000000000 : ℝ)*base71 + (55288796052943/25000000000000000000000000000 : ℝ)*base73 + (296916601102943/50000000000000000000000000000 : ℝ)*base75 + (231753040952943/50000000000000000000000000000 : ℝ)*base77 + (231900244097057/50000000000000000000000000000 : ℝ)*base80 + (1055963052943/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6849069/10000000000000000000000 : ℝ)*base89 + (6849069/10000000000000000000000 : ℝ)*base91 + (6849069/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1059_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1059_s1_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-212899899/1000000000 : ℝ)*x 0 + (5724273853/10000000000 : ℝ)*x 1 + (249221287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212899899/1000000000 : ℝ)^2063 ≤ (12776141679629/100000000000000 : ℝ)^1551 := by
    have hnat : (212899899 : ℕ)^2063*100000000000000^1551 ≤ 12776141679629^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212899899 1000000000 12776141679629 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5724273853/10000000000 : ℝ)^2063 ≤ (11903689458613/25000000000000 : ℝ)^1551 := by
    have hnat : (5724273853 : ℕ)^2063*25000000000000^1551 ≤ 11903689458613^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724273853 10000000000 11903689458613 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249221287/500000000 : ℝ)^2063 ≤ (39609100469821/100000000000000 : ℝ)^1551 := by
    have hnat : (249221287 : ℕ)^2063*100000000000000^1551 ≤ 39609100469821^1551*500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249221287 500000000 39609100469821 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212899899/1000000000 : ℝ), (5724273853/10000000000 : ℝ), (249221287/500000000 : ℝ)] ![(12776141679629/100000000000000 : ℝ), (11903689458613/25000000000000 : ℝ), (39609100469821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212899899/1000000000 : ℝ)|^2063 ≤ (12776141679629/100000000000000 : ℝ)^1551
        have hw : |(-212899899/1000000000 : ℝ)|=(212899899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5724273853/10000000000 : ℝ)|^2063 ≤ (11903689458613/25000000000000 : ℝ)^1551
        have hw : |(5724273853/10000000000 : ℝ)|=(5724273853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249221287/500000000 : ℝ)|^2063 ≤ (39609100469821/100000000000000 : ℝ)^1551
        have hw : |(249221287/500000000 : ℝ)|=(249221287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1084739163/2000000000 : ℝ)*x 0 + (-10119993/40000000 : ℝ)*x 1 + (996885213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084739163/2000000000 : ℝ)^2063 ≤ (44318357698311/100000000000000 : ℝ)^1551 := by
    have hnat : (1084739163 : ℕ)^2063*100000000000000^1551 ≤ 44318357698311^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084739163 2000000000 44318357698311 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10119993/40000000 : ℝ)^2063 ≤ (4018134595989/25000000000000 : ℝ)^1551 := by
    have hnat : (10119993 : ℕ)^2063*25000000000000^1551 ≤ 4018134595989^1551*40000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10119993 40000000 4018134595989 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996885213/2000000000 : ℝ)^2063 ≤ (3960910390501/10000000000000 : ℝ)^1551 := by
    have hnat : (996885213 : ℕ)^2063*10000000000000^1551 ≤ 3960910390501^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996885213 2000000000 3960910390501 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084739163/2000000000 : ℝ), (-10119993/40000000 : ℝ), (996885213/2000000000 : ℝ)] ![(44318357698311/100000000000000 : ℝ), (4018134595989/25000000000000 : ℝ), (3960910390501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084739163/2000000000 : ℝ)|^2063 ≤ (44318357698311/100000000000000 : ℝ)^1551
        have hw : |(1084739163/2000000000 : ℝ)|=(1084739163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10119993/40000000 : ℝ)|^2063 ≤ (4018134595989/25000000000000 : ℝ)^1551
        have hw : |(-10119993/40000000 : ℝ)|=(10119993/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(996885213/2000000000 : ℝ)|^2063 ≤ (3960910390501/10000000000000 : ℝ)^1551
        have hw : |(996885213/2000000000 : ℝ)|=(996885213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (216947853/400000000 : ℝ)*x 0 + (4984425469/10000000000 : ℝ)*x 1 + (-2529998339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216947853/400000000 : ℝ)^2063 ≤ (1772734529653/4000000000000 : ℝ)^1551 := by
    have hnat : (216947853 : ℕ)^2063*4000000000000^1551 ≤ 1772734529653^1551*400000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216947853 400000000 1772734529653 4000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4984425469/10000000000 : ℝ)^2063 ≤ (19804548802701/50000000000000 : ℝ)^1551 := by
    have hnat : (4984425469 : ℕ)^2063*50000000000000^1551 ≤ 19804548802701^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984425469 10000000000 19804548802701 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529998339/10000000000 : ℝ)^2063 ≤ (16072539135997/100000000000000 : ℝ)^1551 := by
    have hnat : (2529998339 : ℕ)^2063*100000000000000^1551 ≤ 16072539135997^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529998339 10000000000 16072539135997 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216947853/400000000 : ℝ), (4984425469/10000000000 : ℝ), (-2529998339/10000000000 : ℝ)] ![(1772734529653/4000000000000 : ℝ), (19804548802701/50000000000000 : ℝ), (16072539135997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216947853/400000000 : ℝ)|^2063 ≤ (1772734529653/4000000000000 : ℝ)^1551
        have hw : |(216947853/400000000 : ℝ)|=(216947853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4984425469/10000000000 : ℝ)|^2063 ≤ (19804548802701/50000000000000 : ℝ)^1551
        have hw : |(4984425469/10000000000 : ℝ)|=(4984425469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2529998339/10000000000 : ℝ)|^2063 ≤ (16072539135997/100000000000000 : ℝ)^1551
        have hw : |(-2529998339/10000000000 : ℝ)|=(2529998339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4324384873/10000000000 : ℝ)*x 0 + (1830605769/5000000000 : ℝ)*x 1 + (5109194777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4324384873/10000000000 : ℝ)^2063 ≤ (1639492637513/5000000000000 : ℝ)^1551 := by
    have hnat : (4324384873 : ℕ)^2063*5000000000000^1551 ≤ 1639492637513^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324384873 10000000000 1639492637513 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830605769/5000000000 : ℝ)^2063 ≤ (26276842868759/100000000000000 : ℝ)^1551 := by
    have hnat : (1830605769 : ℕ)^2063*100000000000000^1551 ≤ 26276842868759^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830605769 5000000000 26276842868759 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5109194777/10000000000 : ℝ)^2063 ≤ (8186660871477/20000000000000 : ℝ)^1551 := by
    have hnat : (5109194777 : ℕ)^2063*20000000000000^1551 ≤ 8186660871477^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109194777 10000000000 8186660871477 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4324384873/10000000000 : ℝ), (1830605769/5000000000 : ℝ), (5109194777/10000000000 : ℝ)] ![(1639492637513/5000000000000 : ℝ), (26276842868759/100000000000000 : ℝ), (8186660871477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4324384873/10000000000 : ℝ)|^2063 ≤ (1639492637513/5000000000000 : ℝ)^1551
        have hw : |(4324384873/10000000000 : ℝ)|=(4324384873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1830605769/5000000000 : ℝ)|^2063 ≤ (26276842868759/100000000000000 : ℝ)^1551
        have hw : |(1830605769/5000000000 : ℝ)|=(1830605769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5109194777/10000000000 : ℝ)|^2063 ≤ (8186660871477/20000000000000 : ℝ)^1551
        have hw : |(5109194777/10000000000 : ℝ)|=(5109194777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129932027/10000000000 : ℝ)*x 0 + (499485019/1000000000 : ℝ)*x 1 + (2856817529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129932027/10000000000 : ℝ)^2063 ≤ (12783589719123/100000000000000 : ℝ)^1551 := by
    have hnat : (2129932027 : ℕ)^2063*100000000000000^1551 ≤ 12783589719123^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129932027 10000000000 12783589719123 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499485019/1000000000 : ℝ)^2063 ≤ (39719322968341/100000000000000 : ℝ)^1551 := by
    have hnat : (499485019 : ℕ)^2063*100000000000000^1551 ≤ 39719322968341^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499485019 1000000000 39719322968341 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856817529/5000000000 : ℝ)^2063 ≤ (47497087294143/100000000000000 : ℝ)^1551 := by
    have hnat : (2856817529 : ℕ)^2063*100000000000000^1551 ≤ 47497087294143^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856817529 5000000000 47497087294143 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129932027/10000000000 : ℝ), (499485019/1000000000 : ℝ), (2856817529/5000000000 : ℝ)] ![(12783589719123/100000000000000 : ℝ), (39719322968341/100000000000000 : ℝ), (47497087294143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129932027/10000000000 : ℝ)|^2063 ≤ (12783589719123/100000000000000 : ℝ)^1551
        have hw : |(-2129932027/10000000000 : ℝ)|=(2129932027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499485019/1000000000 : ℝ)|^2063 ≤ (39719322968341/100000000000000 : ℝ)^1551
        have hw : |(499485019/1000000000 : ℝ)|=(499485019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856817529/5000000000 : ℝ)|^2063 ≤ (47497087294143/100000000000000 : ℝ)^1551
        have hw : |(2856817529/5000000000 : ℝ)|=(2856817529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5234819863/10000000000 : ℝ)*x 0 + (-900393627/5000000000 : ℝ)*x 1 + (5713636599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234819863/10000000000 : ℝ)^2063 ≤ (42277422891371/100000000000000 : ℝ)^1551 := by
    have hnat : (5234819863 : ℕ)^2063*100000000000000^1551 ≤ 42277422891371^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234819863 10000000000 42277422891371 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900393627/5000000000 : ℝ)^2063 ≤ (102254727667/1000000000000 : ℝ)^1551 := by
    have hnat : (900393627 : ℕ)^2063*1000000000000^1551 ≤ 102254727667^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900393627 5000000000 102254727667 1000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5713636599/10000000000 : ℝ)^2063 ≤ (47497104333161/100000000000000 : ℝ)^1551 := by
    have hnat : (5713636599 : ℕ)^2063*100000000000000^1551 ≤ 47497104333161^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5713636599 10000000000 47497104333161 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234819863/10000000000 : ℝ), (-900393627/5000000000 : ℝ), (5713636599/10000000000 : ℝ)] ![(42277422891371/100000000000000 : ℝ), (102254727667/1000000000000 : ℝ), (47497104333161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234819863/10000000000 : ℝ)|^2063 ≤ (42277422891371/100000000000000 : ℝ)^1551
        have hw : |(5234819863/10000000000 : ℝ)|=(5234819863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900393627/5000000000 : ℝ)|^2063 ≤ (102254727667/1000000000000 : ℝ)^1551
        have hw : |(-900393627/5000000000 : ℝ)|=(900393627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5713636599/10000000000 : ℝ)|^2063 ≤ (47497104333161/100000000000000 : ℝ)^1551
        have hw : |(5713636599/10000000000 : ℝ)|=(5713636599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5234817869/10000000000 : ℝ)*x 0 + (1142727759/2000000000 : ℝ)*x 1 + (-2881259/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234817869/10000000000 : ℝ)^2063 ≤ (21138700735689/50000000000000 : ℝ)^1551 := by
    have hnat : (5234817869 : ℕ)^2063*50000000000000^1551 ≤ 21138700735689^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234817869 10000000000 21138700735689 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142727759/2000000000 : ℝ)^2063 ≤ (23748564307297/50000000000000 : ℝ)^1551 := by
    have hnat : (1142727759 : ℕ)^2063*50000000000000^1551 ≤ 23748564307297^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142727759 2000000000 23748564307297 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2881259/16000000 : ℝ)^2063 ≤ (5112734952093/50000000000000 : ℝ)^1551 := by
    have hnat : (2881259 : ℕ)^2063*50000000000000^1551 ≤ 5112734952093^1551*16000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881259 16000000 5112734952093 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234817869/10000000000 : ℝ), (1142727759/2000000000 : ℝ), (-2881259/16000000 : ℝ)] ![(21138700735689/50000000000000 : ℝ), (23748564307297/50000000000000 : ℝ), (5112734952093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234817869/10000000000 : ℝ)|^2063 ≤ (21138700735689/50000000000000 : ℝ)^1551
        have hw : |(5234817869/10000000000 : ℝ)|=(5234817869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142727759/2000000000 : ℝ)|^2063 ≤ (23748564307297/50000000000000 : ℝ)^1551
        have hw : |(1142727759/2000000000 : ℝ)|=(1142727759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2881259/16000000 : ℝ)|^2063 ≤ (5112734952093/50000000000000 : ℝ)^1551
        have hw : |(-2881259/16000000 : ℝ)|=(2881259/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s1_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4326207263/10000000000 : ℝ)*x 0 + (2544394631/5000000000 : ℝ)*x 1 + (736405987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326207263/10000000000 : ℝ)^2063 ≤ (1312329358391/4000000000000 : ℝ)^1551 := by
    have hnat : (4326207263 : ℕ)^2063*4000000000000^1551 ≤ 1312329358391^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326207263 10000000000 1312329358391 4000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544394631/5000000000 : ℝ)^2063 ≤ (40715997868823/100000000000000 : ℝ)^1551 := by
    have hnat : (2544394631 : ℕ)^2063*100000000000000^1551 ≤ 40715997868823^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544394631 5000000000 40715997868823 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736405987/2000000000 : ℝ)^2063 ≤ (5295153629177/20000000000000 : ℝ)^1551 := by
    have hnat : (736405987 : ℕ)^2063*20000000000000^1551 ≤ 5295153629177^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736405987 2000000000 5295153629177 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326207263/10000000000 : ℝ), (2544394631/5000000000 : ℝ), (736405987/2000000000 : ℝ)] ![(1312329358391/4000000000000 : ℝ), (40715997868823/100000000000000 : ℝ), (5295153629177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326207263/10000000000 : ℝ)|^2063 ≤ (1312329358391/4000000000000 : ℝ)^1551
        have hw : |(4326207263/10000000000 : ℝ)|=(4326207263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544394631/5000000000 : ℝ)|^2063 ≤ (40715997868823/100000000000000 : ℝ)^1551
        have hw : |(2544394631/5000000000 : ℝ)|=(2544394631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(736405987/2000000000 : ℝ)|^2063 ≤ (5295153629177/20000000000000 : ℝ)^1551
        have hw : |(736405987/2000000000 : ℝ)|=(736405987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1293/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2603/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (67/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (67/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (67/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (67/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (67/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (67/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (67/100000 : ℝ) ^ (8251/2048 : ℝ) ≤ (3265073/20000000000000000000 : ℝ) := by
    have hpowers : (67/100000 : ℝ)^8251 ≤ (3265073/20000000000000000000 : ℝ)^2048 := by
      have hnat : (67 : ℕ)^8251*20000000000000000000^2048 ≤ 3265073^2048*100000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67 100000 3265073 20000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67/100000 : ℝ)) (X := (3265073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/12500 : ℝ) ^ (8251/2048 : ℝ) ≤ (120840757725699141/20000000000000000000 : ℝ) := by
    have hpowers : (3517/12500 : ℝ)^8251 ≤ (120840757725699141/20000000000000000000 : ℝ)^2048 := by
      have hnat : (3517 : ℕ)^8251*20000000000000000000^2048 ≤ 120840757725699141^2048*12500^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 12500 120840757725699141 20000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/12500 : ℝ)) (X := (120840757725699141/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000003265073/10000000000000000000 : ℝ) ≤ (10000000000000811/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (10000000000003265073/10000000000000000000 : ℝ)^2048 ≤ (10000000000000811/10000000000000000 : ℝ)^8251 := by
      have hnat : (10000000000003265073 : ℕ)^2048*10000000000000000^8251 ≤ 10000000000000811^8251*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000003265073 10000000000000000000 10000000000000811 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000811/10000000000000000 : ℝ)) (X := (10000000000003265073/10000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10060420378864482107/10000000000000000000 : ℝ) ≤ (10014963142320593/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (10060420378864482107/10000000000000000000 : ℝ)^2048 ≤ (10014963142320593/10000000000000000 : ℝ)^8251 := by
      have hnat : (10060420378864482107 : ℕ)^2048*10000000000000000^8251 ≤ 10014963142320593^8251*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10060420378864482107 10000000000000000000 10014963142320593 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014963142320593/10000000000000000 : ℝ)) (X := (10060420378864482107/10000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10120840757725699141/10000000000000000000 : ℝ) ≤ (80239410277123/80000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (10120840757725699141/10000000000000000000 : ℝ)^2048 ≤ (80239410277123/80000000000000 : ℝ)^8251 := by
      have hnat : (10120840757725699141 : ℕ)^2048*80000000000000^8251 ≤ 80239410277123^8251*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10120840757725699141 10000000000000000000 80239410277123 80000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80239410277123/80000000000000 : ℝ)) (X := (10120840757725699141/10000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3265073/20000000000000000000 : ℝ) ≤ ((280687994938951913171/280690000000000000000 : ℝ)+2*(7481571159891/1403450000000000 : ℝ)*(67/100000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (280687994938951913171/280690000000000000000 : ℝ)+2*(7481571159891/1403450000000000 : ℝ)*(67/100000 : ℝ)=(10000000000000811/10000000000000000 : ℝ) by norm_num, show 1+2*(3265073/20000000000000000000 : ℝ)=(10000000000003265073/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(120840757725699141/20000000000000000000 : ℝ)+(3265073/20000000000000000000 : ℝ) ≤ ((280687994938951913171/280690000000000000000 : ℝ)+(7481571159891/1403450000000000 : ℝ)*((3517/12500 : ℝ)+(67/100000 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (280687994938951913171/280690000000000000000 : ℝ)+(7481571159891/1403450000000000 : ℝ)*((3517/12500 : ℝ)+(67/100000 : ℝ))=(10014963142320593/10000000000000000 : ℝ) by norm_num, show 1+(120840757725699141/20000000000000000000 : ℝ)+(3265073/20000000000000000000 : ℝ)=(10060420378864482107/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(120840757725699141/20000000000000000000 : ℝ) ≤ ((280687994938951913171/280690000000000000000 : ℝ)+2*(7481571159891/1403450000000000 : ℝ)*(3517/12500 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (280687994938951913171/280690000000000000000 : ℝ)+2*(7481571159891/1403450000000000 : ℝ)*(3517/12500 : ℝ)=(80239410277123/80000000000000 : ℝ) by norm_num, show 1+2*(120840757725699141/20000000000000000000 : ℝ)=(10120840757725699141/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (280687994938951913171/280690000000000000000 : ℝ)*(X 1 0+X 2 0)+(7481571159891/1403450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (67/100000 : ℝ)) (hi := (3517/12500 : ℝ)) (c := (280687994938951913171/280690000000000000000 : ℝ)) (alpha := (7481571159891/1403450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (280687994938951913171/280690000000000000000 : ℝ)*(X 0 1+X 2 1)+(7481571159891/1403450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (67/100000 : ℝ)) (hi := (3517/12500 : ℝ)) (c := (280687994938951913171/280690000000000000000 : ℝ)) (alpha := (7481571159891/1403450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (280687994938951913171/280690000000000000000 : ℝ)*(X 0 2+X 1 2)+(7481571159891/1403450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (67/100000 : ℝ)) (hi := (3517/12500 : ℝ)) (c := (280687994938951913171/280690000000000000000 : ℝ)) (alpha := (7481571159891/1403450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212899899/1000000000 : ℝ)*X 0 0+(5724273853/10000000000 : ℝ)*X 0 1+(249221287/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1084739163/2000000000 : ℝ)*X 1 0+(-10119993/40000000 : ℝ)*X 1 1+(996885213/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((216947853/400000000 : ℝ)*X 2 0+(4984425469/10000000000 : ℝ)*X 2 1+(-2529998339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4324384873/10000000000 : ℝ)*X 0 0+(1830605769/5000000000 : ℝ)*X 0 1+(5109194777/10000000000 : ℝ)*X 0 2+(4324384873/10000000000 : ℝ)*X 1 0+(1830605769/5000000000 : ℝ)*X 1 1+(5109194777/10000000000 : ℝ)*X 1 2+(4324384873/10000000000 : ℝ)*X 2 0+(1830605769/5000000000 : ℝ)*X 2 1+(5109194777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2129932027/10000000000 : ℝ)*X 0 0+(499485019/1000000000 : ℝ)*X 0 1+(2856817529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5234819863/10000000000 : ℝ)*X 1 0+(-900393627/5000000000 : ℝ)*X 1 1+(5713636599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5234817869/10000000000 : ℝ)*X 2 0+(1142727759/2000000000 : ℝ)*X 2 1+(-2881259/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326207263/10000000000 : ℝ)*X 0 0+(2544394631/5000000000 : ℝ)*X 0 1+(736405987/2000000000 : ℝ)*X 0 2+(4326207263/10000000000 : ℝ)*X 1 0+(2544394631/5000000000 : ℝ)*X 1 1+(736405987/2000000000 : ℝ)*X 1 2+(4326207263/10000000000 : ℝ)*X 2 0+(2544394631/5000000000 : ℝ)*X 2 1+(736405987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2573608973570512480660154589/438578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108839243/100000000000000 : ℝ)*(base1) + (64396213/5000000000000 : ℝ)*(base19) + (1415021477/100000000000000 : ℝ)*(base23) + (1693859/1250000000000 : ℝ)*(upper3) + (140121251/100000000000000 : ℝ)*(upper5) + (63820749342897/6250000000000 : ℝ)*(major0) + (63820749342897/6250000000000 : ℝ)*(major1) + (63820749342897/6250000000000 : ℝ)*(major2) + (1351635150605129/100000000000000 : ℝ)*(sp0) + (54065624498741/4000000000000 : ℝ)*(sp1) + (1351640485371307/100000000000000 : ℝ)*(sp2) + (172654663378829/25000000000000 : ℝ)*(sp3) + (3429313449/50000000000000 : ℝ)*(sp4) + (3120622883/100000000000000 : ℝ)*(sp7) + (690621882977441/100000000000000 : ℝ)*(f.failure) + (84477618774549/6250000000000 : ℝ)*(f.sum) + (628228891713381/140345000000000000000000000000 : ℝ)*base66 + (11658138984485058887/1754312500000000000000000000000000 : ℝ)*base67 + (943295283845683887/1754312500000000000000000000000000 : ℝ)*base69 + (4432238141403246387/1754312500000000000000000000000000 : ℝ)*base71 + (13402098959101/8771562500000000000000000000 : ℝ)*base74 + (6571992773972378613/1754312500000000000000000000000000 : ℝ)*base76 + (7634518250834496387/1754312500000000000000000000000000 : ℝ)*base77 + (6648146460391683887/1754312500000000000000000000000000 : ℝ)*base79 + (29549789841463/4385781250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14423597/10000000000000000000000 : ℝ)*base90 + (14423597/10000000000000000000000 : ℝ)*base92 + (14423597/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25356601922170585919165859/43857812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1902178859/100000000000000 : ℝ)*(base19) + (1849546841/100000000000000 : ℝ)*(base23) + (114412999/50000000000000 : ℝ)*(upper2) + (32436617/10000000000000 : ℝ)*(upper3) + (28919653/6250000000000 : ℝ)*(upper5) + (13138052427911/1250000000000 : ℝ)*(major0) + (13138052427911/1250000000000 : ℝ)*(major1) + (13138052427911/1250000000000 : ℝ)*(major2) + (2418253183/25000000000000 : ℝ)*(sp1) + (10786519871/100000000000000 : ℝ)*(sp2) + (347808993505361/25000000000000 : ℝ)*(sp4) + (347806099707463/25000000000000 : ℝ)*(sp5) + (347805834488683/25000000000000 : ℝ)*(sp6) + (355426197586243/50000000000000 : ℝ)*(sp7) + (355426197586243/50000000000000 : ℝ)*(f.failure) + (347808993505361/25000000000000 : ℝ)*(f.sum) + (52837304706419/14034500000000000000000000000 : ℝ)*base66 + (838731971885234219/350862500000000000000000000000000 : ℝ)*base68 + (2099181809390609219/350862500000000000000000000000000 : ℝ)*base70 + (1937181755532209219/350862500000000000000000000000000 : ℝ)*base72 + (31824234279919/7017250000000000000000000000 : ℝ)*base73 + (28297808845090781/350862500000000000000000000000000 : ℝ)*base75 + (3576345858976746719/350862500000000000000000000000000 : ℝ)*base78 + (2582009172253371719/350862500000000000000000000000000 : ℝ)*base80 + (77347822735203/28069000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13660569/5000000000000000000000 : ℝ)*base89 + (13660569/5000000000000000000000 : ℝ)*base91 + (13660569/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1059_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1293/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2603/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1059_s2_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-437362661/2000000000 : ℝ)*x 0 + (5527351939/10000000000 : ℝ)*x 1 + (5144674983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437362661/2000000000 : ℝ)^2063 ≤ (13239671511559/100000000000000 : ℝ)^1551 := by
    have hnat : (437362661 : ℕ)^2063*100000000000000^1551 ≤ 13239671511559^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437362661 2000000000 13239671511559 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527351939/10000000000 : ℝ)^2063 ≤ (22724249523061/50000000000000 : ℝ)^1551 := by
    have hnat : (5527351939 : ℕ)^2063*50000000000000^1551 ≤ 22724249523061^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527351939 10000000000 22724249523061 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144674983/10000000000 : ℝ)^2063 ≤ (4131182942361/10000000000000 : ℝ)^1551 := by
    have hnat : (5144674983 : ℕ)^2063*10000000000000^1551 ≤ 4131182942361^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144674983 10000000000 4131182942361 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437362661/2000000000 : ℝ), (5527351939/10000000000 : ℝ), (5144674983/10000000000 : ℝ)] ![(13239671511559/100000000000000 : ℝ), (22724249523061/50000000000000 : ℝ), (4131182942361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437362661/2000000000 : ℝ)|^2063 ≤ (13239671511559/100000000000000 : ℝ)^1551
        have hw : |(-437362661/2000000000 : ℝ)|=(437362661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527351939/10000000000 : ℝ)|^2063 ≤ (22724249523061/50000000000000 : ℝ)^1551
        have hw : |(5527351939/10000000000 : ℝ)|=(5527351939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144674983/10000000000 : ℝ)|^2063 ≤ (4131182942361/10000000000000 : ℝ)^1551
        have hw : |(5144674983/10000000000 : ℝ)|=(5144674983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5377515611/10000000000 : ℝ)*x 0 + (-477288341/2000000000 : ℝ)*x 1 + (1286169097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377515611/10000000000 : ℝ)^2063 ≤ (21908573879851/50000000000000 : ℝ)^1551 := by
    have hnat : (5377515611 : ℕ)^2063*50000000000000^1551 ≤ 21908573879851^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377515611 10000000000 21908573879851 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477288341/2000000000 : ℝ)^2063 ≤ (14871007796299/100000000000000 : ℝ)^1551 := by
    have hnat : (477288341 : ℕ)^2063*100000000000000^1551 ≤ 14871007796299^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477288341 2000000000 14871007796299 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286169097/2500000000 : ℝ)^2063 ≤ (2065592221507/5000000000000 : ℝ)^1551 := by
    have hnat : (1286169097 : ℕ)^2063*5000000000000^1551 ≤ 2065592221507^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286169097 2500000000 2065592221507 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377515611/10000000000 : ℝ), (-477288341/2000000000 : ℝ), (1286169097/2500000000 : ℝ)] ![(21908573879851/50000000000000 : ℝ), (14871007796299/100000000000000 : ℝ), (2065592221507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377515611/10000000000 : ℝ)|^2063 ≤ (21908573879851/50000000000000 : ℝ)^1551
        have hw : |(5377515611/10000000000 : ℝ)|=(5377515611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-477288341/2000000000 : ℝ)|^2063 ≤ (14871007796299/100000000000000 : ℝ)^1551
        have hw : |(-477288341/2000000000 : ℝ)|=(477288341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1286169097/2500000000 : ℝ)|^2063 ≤ (2065592221507/5000000000000 : ℝ)^1551
        have hw : |(1286169097/2500000000 : ℝ)|=(1286169097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5377515801/10000000000 : ℝ)*x 0 + (643084509/1250000000 : ℝ)*x 1 + (-2386441863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377515801/10000000000 : ℝ)^2063 ≤ (21908574909463/50000000000000 : ℝ)^1551 := by
    have hnat : (5377515801 : ℕ)^2063*50000000000000^1551 ≤ 21908574909463^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377515801 10000000000 21908574909463 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643084509/1250000000 : ℝ)^2063 ≤ (8262368211001/20000000000000 : ℝ)^1551 := by
    have hnat : (643084509 : ℕ)^2063*20000000000000^1551 ≤ 8262368211001^1551*1250000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643084509 1250000000 8262368211001 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386441863/10000000000 : ℝ)^2063 ≤ (7435504552943/50000000000000 : ℝ)^1551 := by
    have hnat : (2386441863 : ℕ)^2063*50000000000000^1551 ≤ 7435504552943^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386441863 10000000000 7435504552943 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377515801/10000000000 : ℝ), (643084509/1250000000 : ℝ), (-2386441863/10000000000 : ℝ)] ![(21908574909463/50000000000000 : ℝ), (8262368211001/20000000000000 : ℝ), (7435504552943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377515801/10000000000 : ℝ)|^2063 ≤ (21908574909463/50000000000000 : ℝ)^1551
        have hw : |(5377515801/10000000000 : ℝ)|=(5377515801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643084509/1250000000 : ℝ)|^2063 ≤ (8262368211001/20000000000000 : ℝ)^1551
        have hw : |(643084509/1250000000 : ℝ)|=(643084509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2386441863/10000000000 : ℝ)|^2063 ≤ (7435504552943/50000000000000 : ℝ)^1551
        have hw : |(-2386441863/10000000000 : ℝ)|=(2386441863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4363814957/10000000000 : ℝ)*x 0 + (125174061/312500000 : ℝ)*x 1 + (2377257079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363814957/10000000000 : ℝ)^2063 ≤ (3318812683657/10000000000000 : ℝ)^1551 := by
    have hnat : (4363814957 : ℕ)^2063*10000000000000^1551 ≤ 3318812683657^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363814957 10000000000 3318812683657 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125174061/312500000 : ℝ)^2063 ≤ (14807099678189/50000000000000 : ℝ)^1551 := by
    have hnat : (125174061 : ℕ)^2063*50000000000000^1551 ≤ 14807099678189^1551*312500000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125174061 312500000 14807099678189 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2377257079/5000000000 : ℝ)^2063 ≤ (37197673789069/100000000000000 : ℝ)^1551 := by
    have hnat : (2377257079 : ℕ)^2063*100000000000000^1551 ≤ 37197673789069^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377257079 5000000000 37197673789069 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363814957/10000000000 : ℝ), (125174061/312500000 : ℝ), (2377257079/5000000000 : ℝ)] ![(3318812683657/10000000000000 : ℝ), (14807099678189/50000000000000 : ℝ), (37197673789069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363814957/10000000000 : ℝ)|^2063 ≤ (3318812683657/10000000000000 : ℝ)^1551
        have hw : |(4363814957/10000000000 : ℝ)|=(4363814957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125174061/312500000 : ℝ)|^2063 ≤ (14807099678189/50000000000000 : ℝ)^1551
        have hw : |(125174061/312500000 : ℝ)|=(125174061/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2377257079/5000000000 : ℝ)|^2063 ≤ (37197673789069/100000000000000 : ℝ)^1551
        have hw : |(2377257079/5000000000 : ℝ)|=(2377257079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186941343/10000000000 : ℝ)*x 0 + (643434211/1250000000 : ℝ)*x 1 + (5524523979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186941343/10000000000 : ℝ)^2063 ≤ (13240702600221/100000000000000 : ℝ)^1551 := by
    have hnat : (2186941343 : ℕ)^2063*100000000000000^1551 ≤ 13240702600221^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186941343 10000000000 13240702600221 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643434211/1250000000 : ℝ)^2063 ≤ (41341724524731/100000000000000 : ℝ)^1551 := by
    have hnat : (643434211 : ℕ)^2063*100000000000000^1551 ≤ 41341724524731^1551*1250000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643434211 1250000000 41341724524731 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5524523979/10000000000 : ℝ)^2063 ≤ (45417572854753/100000000000000 : ℝ)^1551 := by
    have hnat : (5524523979 : ℕ)^2063*100000000000000^1551 ≤ 45417572854753^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524523979 10000000000 45417572854753 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186941343/10000000000 : ℝ), (643434211/1250000000 : ℝ), (5524523979/10000000000 : ℝ)] ![(13240702600221/100000000000000 : ℝ), (41341724524731/100000000000000 : ℝ), (45417572854753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186941343/10000000000 : ℝ)|^2063 ≤ (13240702600221/100000000000000 : ℝ)^1551
        have hw : |(-2186941343/10000000000 : ℝ)|=(2186941343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643434211/1250000000 : ℝ)|^2063 ≤ (41341724524731/100000000000000 : ℝ)^1551
        have hw : |(643434211/1250000000 : ℝ)|=(643434211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5524523979/10000000000 : ℝ)|^2063 ≤ (45417572854753/100000000000000 : ℝ)^1551
        have hw : |(5524523979/10000000000 : ℝ)|=(5524523979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5280971993/10000000000 : ℝ)*x 0 + (-100329751/500000000 : ℝ)*x 1 + (5524524057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280971993/10000000000 : ℝ)^2063 ≤ (42773919430429/100000000000000 : ℝ)^1551 := by
    have hnat : (5280971993 : ℕ)^2063*100000000000000^1551 ≤ 42773919430429^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280971993 10000000000 42773919430429 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100329751/500000000 : ℝ)^2063 ≤ (1180850685123/10000000000000 : ℝ)^1551 := by
    have hnat : (100329751 : ℕ)^2063*10000000000000^1551 ≤ 1180850685123^1551*500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100329751 500000000 1180850685123 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5524524057/10000000000 : ℝ)^2063 ≤ (45417573707679/100000000000000 : ℝ)^1551 := by
    have hnat : (5524524057 : ℕ)^2063*100000000000000^1551 ≤ 45417573707679^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524524057 10000000000 45417573707679 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280971993/10000000000 : ℝ), (-100329751/500000000 : ℝ), (5524524057/10000000000 : ℝ)] ![(42773919430429/100000000000000 : ℝ), (1180850685123/10000000000000 : ℝ), (45417573707679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280971993/10000000000 : ℝ)|^2063 ≤ (42773919430429/100000000000000 : ℝ)^1551
        have hw : |(5280971993/10000000000 : ℝ)|=(5280971993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100329751/500000000 : ℝ)|^2063 ≤ (1180850685123/10000000000000 : ℝ)^1551
        have hw : |(-100329751/500000000 : ℝ)|=(100329751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5524524057/10000000000 : ℝ)|^2063 ≤ (45417573707679/100000000000000 : ℝ)^1551
        have hw : |(5524524057/10000000000 : ℝ)|=(5524524057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2640486117/5000000000 : ℝ)*x 0 + (5524523893/10000000000 : ℝ)*x 1 + (-2006594917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640486117/5000000000 : ℝ)^2063 ≤ (42773922026817/100000000000000 : ℝ)^1551 := by
    have hnat : (2640486117 : ℕ)^2063*100000000000000^1551 ≤ 42773922026817^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640486117 5000000000 42773922026817 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524523893/10000000000 : ℝ)^2063 ≤ (11354392978587/25000000000000 : ℝ)^1551 := by
    have hnat : (5524523893 : ℕ)^2063*25000000000000^1551 ≤ 11354392978587^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524523893 10000000000 11354392978587 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006594917/10000000000 : ℝ)^2063 ≤ (5904253022499/50000000000000 : ℝ)^1551 := by
    have hnat : (2006594917 : ℕ)^2063*50000000000000^1551 ≤ 5904253022499^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006594917 10000000000 5904253022499 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640486117/5000000000 : ℝ), (5524523893/10000000000 : ℝ), (-2006594917/10000000000 : ℝ)] ![(42773922026817/100000000000000 : ℝ), (11354392978587/25000000000000 : ℝ), (5904253022499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640486117/5000000000 : ℝ)|^2063 ≤ (42773922026817/100000000000000 : ℝ)^1551
        have hw : |(2640486117/5000000000 : ℝ)|=(2640486117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524523893/10000000000 : ℝ)|^2063 ≤ (11354392978587/25000000000000 : ℝ)^1551
        have hw : |(5524523893/10000000000 : ℝ)|=(5524523893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006594917/10000000000 : ℝ)|^2063 ≤ (5904253022499/50000000000000 : ℝ)^1551
        have hw : |(-2006594917/10000000000 : ℝ)|=(2006594917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s2_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1091016193/2500000000 : ℝ)*x 0 + (4749041471/10000000000 : ℝ)*x 1 + (4011101889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091016193/2500000000 : ℝ)^2063 ≤ (16595326980017/50000000000000 : ℝ)^1551 := by
    have hnat : (1091016193 : ℕ)^2063*50000000000000^1551 ≤ 16595326980017^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091016193 2500000000 16595326980017 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4749041471/10000000000 : ℝ)^2063 ≤ (18570367046953/50000000000000 : ℝ)^1551 := by
    have hnat : (4749041471 : ℕ)^2063*50000000000000^1551 ≤ 18570367046953^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749041471 10000000000 18570367046953 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4011101889/10000000000 : ℝ)^2063 ≤ (14834305966191/50000000000000 : ℝ)^1551 := by
    have hnat : (4011101889 : ℕ)^2063*50000000000000^1551 ≤ 14834305966191^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011101889 10000000000 14834305966191 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091016193/2500000000 : ℝ), (4749041471/10000000000 : ℝ), (4011101889/10000000000 : ℝ)] ![(16595326980017/50000000000000 : ℝ), (18570367046953/50000000000000 : ℝ), (14834305966191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091016193/2500000000 : ℝ)|^2063 ≤ (16595326980017/50000000000000 : ℝ)^1551
        have hw : |(1091016193/2500000000 : ℝ)|=(1091016193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4749041471/10000000000 : ℝ)|^2063 ≤ (18570367046953/50000000000000 : ℝ)^1551
        have hw : |(4749041471/10000000000 : ℝ)|=(4749041471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4011101889/10000000000 : ℝ)|^2063 ≤ (14834305966191/50000000000000 : ℝ)^1551
        have hw : |(4011101889/10000000000 : ℝ)|=(4011101889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2603/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1293/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8677/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4191/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2603/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1293/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2603/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1293/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2603/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1293/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2603/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1293/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2603/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1293/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2603/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1293/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1293/25000 : ℝ) ^ (8251/2048 : ℝ) ≤ (657016650135767/100000000000000000000 : ℝ) := by
    have hpowers : (1293/25000 : ℝ)^8251 ≤ (657016650135767/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1293 : ℕ)^8251*100000000000000000000^2048 ≤ 657016650135767^2048*25000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1293 25000 657016650135767 100000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1293/25000 : ℝ)) (X := (657016650135767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2603/12500 : ℝ) ^ (8251/2048 : ℝ) ≤ (11233250128185401/6250000000000000000 : ℝ) := by
    have hpowers : (2603/12500 : ℝ)^8251 ≤ (11233250128185401/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2603 : ℕ)^8251*6250000000000000000^2048 ≤ 11233250128185401^2048*12500^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2603 12500 11233250128185401 6250000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2603/12500 : ℝ)) (X := (11233250128185401/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000657016650135767/50000000000000000000 : ℝ) ≤ (10000032615766653/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (50000657016650135767/50000000000000000000 : ℝ)^2048 ≤ (10000032615766653/10000000000000000 : ℝ)^8251 := by
      have hnat : (50000657016650135767 : ℕ)^2048*10000000000000000^8251 ≤ 10000032615766653^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000657016650135767 50000000000000000000 10000032615766653 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032615766653/10000000000000000 : ℝ)) (X := (50000657016650135767/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100180389018701102183/100000000000000000000 : ℝ) ≤ (39079978301373/39062500000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (100180389018701102183/100000000000000000000 : ℝ)^2048 ≤ (39079978301373/39062500000000 : ℝ)^8251 := by
      have hnat : (100180389018701102183 : ℕ)^2048*39062500000000^8251 ≤ 39079978301373^8251*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100180389018701102183 100000000000000000000 39079978301373 39062500000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39079978301373/39062500000000 : ℝ)) (X := (100180389018701102183/100000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3136233250128185401/3125000000000000000 : ℝ) ≤ (10008916274536323/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (3136233250128185401/3125000000000000000 : ℝ)^2048 ≤ (10008916274536323/10000000000000000 : ℝ)^8251 := by
      have hnat : (3136233250128185401 : ℕ)^2048*10000000000000000^8251 ≤ 10008916274536323^8251*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3136233250128185401 3125000000000000000 10008916274536323 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008916274536323/10000000000000000 : ℝ)) (X := (3136233250128185401/3125000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(657016650135767/100000000000000000000 : ℝ) ≤ ((39118641054705729879/39130000000000000000 : ℝ)+2*(888365876967/313040000000000 : ℝ)*(1293/25000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (39118641054705729879/39130000000000000000 : ℝ)+2*(888365876967/313040000000000 : ℝ)*(1293/25000 : ℝ)=(10000032615766653/10000000000000000 : ℝ) by norm_num, show 1+2*(657016650135767/100000000000000000000 : ℝ)=(50000657016650135767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11233250128185401/6250000000000000000 : ℝ)+(657016650135767/100000000000000000000 : ℝ) ≤ ((39118641054705729879/39130000000000000000 : ℝ)+(888365876967/313040000000000 : ℝ)*((2603/12500 : ℝ)+(1293/25000 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (39118641054705729879/39130000000000000000 : ℝ)+(888365876967/313040000000000 : ℝ)*((2603/12500 : ℝ)+(1293/25000 : ℝ))=(39079978301373/39062500000000 : ℝ) by norm_num, show 1+(11233250128185401/6250000000000000000 : ℝ)+(657016650135767/100000000000000000000 : ℝ)=(100180389018701102183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11233250128185401/6250000000000000000 : ℝ) ≤ ((39118641054705729879/39130000000000000000 : ℝ)+2*(888365876967/313040000000000 : ℝ)*(2603/12500 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (39118641054705729879/39130000000000000000 : ℝ)+2*(888365876967/313040000000000 : ℝ)*(2603/12500 : ℝ)=(10008916274536323/10000000000000000 : ℝ) by norm_num, show 1+2*(11233250128185401/6250000000000000000 : ℝ)=(3136233250128185401/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39118641054705729879/39130000000000000000 : ℝ)*(X 1 0+X 2 0)+(888365876967/313040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (1293/25000 : ℝ)) (hi := (2603/12500 : ℝ)) (c := (39118641054705729879/39130000000000000000 : ℝ)) (alpha := (888365876967/313040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39118641054705729879/39130000000000000000 : ℝ)*(X 0 1+X 2 1)+(888365876967/313040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (1293/25000 : ℝ)) (hi := (2603/12500 : ℝ)) (c := (39118641054705729879/39130000000000000000 : ℝ)) (alpha := (888365876967/313040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39118641054705729879/39130000000000000000 : ℝ)*(X 0 2+X 1 2)+(888365876967/313040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (1293/25000 : ℝ)) (hi := (2603/12500 : ℝ)) (c := (39118641054705729879/39130000000000000000 : ℝ)) (alpha := (888365876967/313040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437362661/2000000000 : ℝ)*X 0 0+(5527351939/10000000000 : ℝ)*X 0 1+(5144674983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377515611/10000000000 : ℝ)*X 1 0+(-477288341/2000000000 : ℝ)*X 1 1+(1286169097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377515801/10000000000 : ℝ)*X 2 0+(643084509/1250000000 : ℝ)*X 2 1+(-2386441863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363814957/10000000000 : ℝ)*X 0 0+(125174061/312500000 : ℝ)*X 0 1+(2377257079/5000000000 : ℝ)*X 0 2+(4363814957/10000000000 : ℝ)*X 1 0+(125174061/312500000 : ℝ)*X 1 1+(2377257079/5000000000 : ℝ)*X 1 2+(4363814957/10000000000 : ℝ)*X 2 0+(125174061/312500000 : ℝ)*X 2 1+(2377257079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2186941343/10000000000 : ℝ)*X 0 0+(643434211/1250000000 : ℝ)*X 0 1+(5524523979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280971993/10000000000 : ℝ)*X 1 0+(-100329751/500000000 : ℝ)*X 1 1+(5524524057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640486117/5000000000 : ℝ)*X 2 0+(5524523893/10000000000 : ℝ)*X 2 1+(-2006594917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091016193/2500000000 : ℝ)*X 0 0+(4749041471/10000000000 : ℝ)*X 0 1+(4011101889/10000000000 : ℝ)*X 0 2+(1091016193/2500000000 : ℝ)*X 1 0+(4749041471/10000000000 : ℝ)*X 1 1+(4011101889/10000000000 : ℝ)*X 1 2+(1091016193/2500000000 : ℝ)*X 2 0+(4749041471/10000000000 : ℝ)*X 2 1+(4011101889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5186307662594038344524006163/978250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191135831/100000000000000 : ℝ)*(base1) + (2759133061/100000000000000 : ℝ)*(base19) + (570292939/20000000000000 : ℝ)*(base23) + (38932949/12500000000000 : ℝ)*(upper3) + (119734161/50000000000000 : ℝ)*(upper5) + (987118471118867/50000000000000 : ℝ)*(major0) + (987118471118867/50000000000000 : ℝ)*(major1) + (987118471118867/50000000000000 : ℝ)*(major2) + (1306602346109963/50000000000000 : ℝ)*(sp0) + (261323588740539/10000000000000 : ℝ)*(sp1) + (653308948768439/25000000000000 : ℝ)*(sp2) + (133522347241679/10000000000000 : ℝ)*(sp3) + (6829090871/20000000000000 : ℝ)*(sp4) + (2279532759/20000000000000 : ℝ)*(sp7) + (41726095663013/3125000000000 : ℝ)*(f.failure) + (52264772930769/2000000000000 : ℝ)*(f.sum) + (11246541018439/7826000000000000000000000000 : ℝ)*base65 + (4313377223383950299/279500000000000000000000000000000 : ℝ)*base67 + (961465899213450299/279500000000000000000000000000000 : ℝ)*base69 + (1569241533094450299/279500000000000000000000000000000 : ℝ)*base71 + (46390735740439/7826000000000000000000000000 : ℝ)*base73 + (837607845211950299/279500000000000000000000000000000 : ℝ)*base75 + (2172996396247450299/279500000000000000000000000000000 : ℝ)*base77 + (229793152882950299/279500000000000000000000000000000 : ℝ)*base79 + (3539256961967/7826000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1818479/312500000000000000000 : ℝ)*base89 + (1818479/312500000000000000000 : ℝ)*base91 + (1818479/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14811228601214793675525010353/1956500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (732526423/50000000000000 : ℝ)*(base19) + (1697450103/100000000000000 : ℝ)*(base23) + (9891999/5000000000000 : ℝ)*(upper3) + (3844037/10000000000000 : ℝ)*(lower4) + (162700039/100000000000000 : ℝ)*(upper5) + (2003645412145731/100000000000000 : ℝ)*(major0) + (2003645412145731/100000000000000 : ℝ)*(major1) + (2003645412145731/100000000000000 : ℝ)*(major2) + (12597886709/100000000000000 : ℝ)*(sp1) + (588316257/4000000000000 : ℝ)*(sp2) + (132608284468273/5000000000000 : ℝ)*(sp4) + (165759476651619/6250000000000 : ℝ)*(sp5) + (663037321002233/25000000000000 : ℝ)*(sp6) + (677562441291871/50000000000000 : ℝ)*(sp7) + (677562441291871/50000000000000 : ℝ)*(f.failure) + (132608284468273/5000000000000 : ℝ)*(f.sum) + (16464625141189/15652000000000000000000000000 : ℝ)*base65 + (1641839454814625493/559000000000000000000000000000000 : ℝ)*base68 + (1166283070758625493/559000000000000000000000000000000 : ℝ)*base70 + (5641719951438374507/559000000000000000000000000000000 : ℝ)*base71 + (60359202324287/15652000000000000000000000000 : ℝ)*base74 + (7217076666721374507/559000000000000000000000000000000 : ℝ)*base75 + (500991246560374507/559000000000000000000000000000000 : ℝ)*base77 + (1261629801821374507/559000000000000000000000000000000 : ℝ)*base79 + (43083348989911/15652000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10701907/5000000000000000000000 : ℝ)*base90 + (10701907/5000000000000000000000 : ℝ)*base92 + (10701907/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1059_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2603/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1293/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4191/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1059_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4191/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1059_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1059_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1059_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4191/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1059_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
