-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:49.674544+00:00
-- url     : https://prove2.me/submissions/da15a34d-e6da-4dd3-95e1-4968ea5d7205

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
theorem support_rectangle_w1266_s3_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526577211/2500000000 : ℝ)*x 0 + (216703581/400000000 : ℝ)*x 1 + (1310606813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526577211/2500000000 : ℝ)^8459 ≤ (6403103716421/50000000000000 : ℝ)^6411 := by
    have hnat : (526577211 : ℕ)^8459*50000000000000^6411 ≤ 6403103716421^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526577211 2500000000 6403103716421 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216703581/400000000 : ℝ)^8459 ≤ (8908410041223/20000000000000 : ℝ)^6411 := by
    have hnat : (216703581 : ℕ)^8459*20000000000000^6411 ≤ 8908410041223^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216703581 400000000 8908410041223 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310606813/2500000000 : ℝ)^8459 ≤ (8530348470563/20000000000000 : ℝ)^6411 := by
    have hnat : (1310606813 : ℕ)^8459*20000000000000^6411 ≤ 8530348470563^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310606813 2500000000 8530348470563 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526577211/2500000000 : ℝ), (216703581/400000000 : ℝ), (1310606813/2500000000 : ℝ)] ![(6403103716421/50000000000000 : ℝ), (8908410041223/20000000000000 : ℝ), (8530348470563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526577211/2500000000 : ℝ)|^8459 ≤ (6403103716421/50000000000000 : ℝ)^6411
        have hw : |(-526577211/2500000000 : ℝ)|=(526577211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216703581/400000000 : ℝ)|^8459 ≤ (8908410041223/20000000000000 : ℝ)^6411
        have hw : |(216703581/400000000 : ℝ)|=(216703581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310606813/2500000000 : ℝ)|^8459 ≤ (8530348470563/20000000000000 : ℝ)^6411
        have hw : |(1310606813/2500000000 : ℝ)|=(1310606813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5350964513/10000000000 : ℝ)*x 0 + (-2195627427/10000000000 : ℝ)*x 1 + (5242427369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350964513/10000000000 : ℝ)^8459 ≤ (876414259817/2000000000000 : ℝ)^6411 := by
    have hnat : (5350964513 : ℕ)^8459*2000000000000^6411 ≤ 876414259817^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350964513 10000000000 876414259817 2000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195627427/10000000000 : ℝ)^8459 ≤ (6763771695917/50000000000000 : ℝ)^6411 := by
    have hnat : (2195627427 : ℕ)^8459*50000000000000^6411 ≤ 6763771695917^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195627427 10000000000 6763771695917 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242427369/10000000000 : ℝ)^8459 ≤ (42651743608797/100000000000000 : ℝ)^6411 := by
    have hnat : (5242427369 : ℕ)^8459*100000000000000^6411 ≤ 42651743608797^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242427369 10000000000 42651743608797 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350964513/10000000000 : ℝ), (-2195627427/10000000000 : ℝ), (5242427369/10000000000 : ℝ)] ![(876414259817/2000000000000 : ℝ), (6763771695917/50000000000000 : ℝ), (42651743608797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350964513/10000000000 : ℝ)|^8459 ≤ (876414259817/2000000000000 : ℝ)^6411
        have hw : |(5350964513/10000000000 : ℝ)|=(5350964513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195627427/10000000000 : ℝ)|^8459 ≤ (6763771695917/50000000000000 : ℝ)^6411
        have hw : |(-2195627427/10000000000 : ℝ)|=(2195627427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242427369/10000000000 : ℝ)|^8459 ≤ (42651743608797/100000000000000 : ℝ)^6411
        have hw : |(5242427369/10000000000 : ℝ)|=(5242427369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10701929/20000000 : ℝ)*x 0 + (2621213919/5000000000 : ℝ)*x 1 + (-274453353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10701929/20000000 : ℝ)^8459 ≤ (2191035642519/5000000000000 : ℝ)^6411 := by
    have hnat : (10701929 : ℕ)^8459*5000000000000^6411 ≤ 2191035642519^6411*20000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10701929 20000000 2191035642519 5000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621213919/5000000000 : ℝ)^8459 ≤ (42651748643461/100000000000000 : ℝ)^6411 := by
    have hnat : (2621213919 : ℕ)^8459*100000000000000^6411 ≤ 42651748643461^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621213919 5000000000 42651748643461 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274453353/1250000000 : ℝ)^8459 ≤ (6763769244931/50000000000000 : ℝ)^6411 := by
    have hnat : (274453353 : ℕ)^8459*50000000000000^6411 ≤ 6763769244931^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274453353 1250000000 6763769244931 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10701929/20000000 : ℝ), (2621213919/5000000000 : ℝ), (-274453353/1250000000 : ℝ)] ![(2191035642519/5000000000000 : ℝ), (42651748643461/100000000000000 : ℝ), (6763769244931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10701929/20000000 : ℝ)|^8459 ≤ (2191035642519/5000000000000 : ℝ)^6411
        have hw : |(10701929/20000000 : ℝ)|=(10701929/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621213919/5000000000 : ℝ)|^8459 ≤ (42651748643461/100000000000000 : ℝ)^6411
        have hw : |(2621213919/5000000000 : ℝ)|=(2621213919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274453353/1250000000 : ℝ)|^8459 ≤ (6763769244931/50000000000000 : ℝ)^6411
        have hw : |(-274453353/1250000000 : ℝ)|=(274453353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543238291/1250000000 : ℝ)*x 0 + (4170959613/10000000000 : ℝ)*x 1 + (181117367/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543238291/1250000000 : ℝ)^8459 ≤ (33301576315823/100000000000000 : ℝ)^6411 := by
    have hnat : (543238291 : ℕ)^8459*100000000000000^6411 ≤ 33301576315823^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543238291 1250000000 33301576315823 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170959613/10000000000 : ℝ)^8459 ≤ (6308847174871/20000000000000 : ℝ)^6411 := by
    have hnat : (4170959613 : ℕ)^8459*20000000000000^6411 ≤ 6308847174871^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170959613 10000000000 6308847174871 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181117367/400000000 : ℝ)^8459 ≤ (35154187790821/100000000000000 : ℝ)^6411 := by
    have hnat : (181117367 : ℕ)^8459*100000000000000^6411 ≤ 35154187790821^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181117367 400000000 35154187790821 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543238291/1250000000 : ℝ), (4170959613/10000000000 : ℝ), (181117367/400000000 : ℝ)] ![(33301576315823/100000000000000 : ℝ), (6308847174871/20000000000000 : ℝ), (35154187790821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543238291/1250000000 : ℝ)|^8459 ≤ (33301576315823/100000000000000 : ℝ)^6411
        have hw : |(543238291/1250000000 : ℝ)|=(543238291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170959613/10000000000 : ℝ)|^8459 ≤ (6308847174871/20000000000000 : ℝ)^6411
        have hw : |(4170959613/10000000000 : ℝ)|=(4170959613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181117367/400000000 : ℝ)|^8459 ≤ (35154187790821/100000000000000 : ℝ)^6411
        have hw : |(181117367/400000000 : ℝ)|=(181117367/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106322727/10000000000 : ℝ)*x 0 + (1048610903/2000000000 : ℝ)*x 1 + (5416958523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106322727/10000000000 : ℝ)^8459 ≤ (1600789850589/12500000000000 : ℝ)^6411 := by
    have hnat : (2106322727 : ℕ)^8459*12500000000000^6411 ≤ 1600789850589^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106322727 10000000000 1600789850589 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048610903/2000000000 : ℝ)^8459 ≤ (42658476081023/100000000000000 : ℝ)^6411 := by
    have hnat : (1048610903 : ℕ)^8459*100000000000000^6411 ≤ 42658476081023^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048610903 2000000000 42658476081023 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416958523/10000000000 : ℝ)^8459 ≤ (44535205102753/100000000000000 : ℝ)^6411 := by
    have hnat : (5416958523 : ℕ)^8459*100000000000000^6411 ≤ 44535205102753^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416958523 10000000000 44535205102753 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106322727/10000000000 : ℝ), (1048610903/2000000000 : ℝ), (5416958523/10000000000 : ℝ)] ![(1600789850589/12500000000000 : ℝ), (42658476081023/100000000000000 : ℝ), (44535205102753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106322727/10000000000 : ℝ)|^8459 ≤ (1600789850589/12500000000000 : ℝ)^6411
        have hw : |(-2106322727/10000000000 : ℝ)|=(2106322727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048610903/2000000000 : ℝ)|^8459 ≤ (42658476081023/100000000000000 : ℝ)^6411
        have hw : |(1048610903/2000000000 : ℝ)|=(1048610903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416958523/10000000000 : ℝ)|^8459 ≤ (44535205102753/100000000000000 : ℝ)^6411
        have hw : |(5416958523/10000000000 : ℝ)|=(5416958523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061241181/2000000000 : ℝ)*x 0 + (-2021095551/10000000000 : ℝ)*x 1 + (5416958361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061241181/2000000000 : ℝ)^8459 ≤ (21668862985043/50000000000000 : ℝ)^6411 := by
    have hnat : (1061241181 : ℕ)^8459*50000000000000^6411 ≤ 21668862985043^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061241181 2000000000 21668862985043 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2021095551/10000000000 : ℝ)^8459 ≤ (2425414135811/20000000000000 : ℝ)^6411 := by
    have hnat : (2021095551 : ℕ)^8459*20000000000000^6411 ≤ 2425414135811^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021095551 10000000000 2425414135811 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416958361/10000000000 : ℝ)^8459 ≤ (44535203345411/100000000000000 : ℝ)^6411 := by
    have hnat : (5416958361 : ℕ)^8459*100000000000000^6411 ≤ 44535203345411^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416958361 10000000000 44535203345411 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061241181/2000000000 : ℝ), (-2021095551/10000000000 : ℝ), (5416958361/10000000000 : ℝ)] ![(21668862985043/50000000000000 : ℝ), (2425414135811/20000000000000 : ℝ), (44535203345411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061241181/2000000000 : ℝ)|^8459 ≤ (21668862985043/50000000000000 : ℝ)^6411
        have hw : |(1061241181/2000000000 : ℝ)|=(1061241181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2021095551/10000000000 : ℝ)|^8459 ≤ (2425414135811/20000000000000 : ℝ)^6411
        have hw : |(-2021095551/10000000000 : ℝ)|=(2021095551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416958361/10000000000 : ℝ)|^8459 ≤ (44535203345411/100000000000000 : ℝ)^6411
        have hw : |(5416958361/10000000000 : ℝ)|=(5416958361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663275653/1250000000 : ℝ)*x 0 + (1354239701/2500000000 : ℝ)*x 1 + (-202109587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663275653/1250000000 : ℝ)^8459 ≤ (43337718631331/100000000000000 : ℝ)^6411 := by
    have hnat : (663275653 : ℕ)^8459*100000000000000^6411 ≤ 43337718631331^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663275653 1250000000 43337718631331 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354239701/2500000000 : ℝ)^8459 ≤ (44535208150981/100000000000000 : ℝ)^6411 := by
    have hnat : (1354239701 : ℕ)^8459*100000000000000^6411 ≤ 44535208150981^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354239701 2500000000 44535208150981 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202109587/1000000000 : ℝ)^8459 ≤ (3031768301147/25000000000000 : ℝ)^6411 := by
    have hnat : (202109587 : ℕ)^8459*25000000000000^6411 ≤ 3031768301147^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202109587 1000000000 3031768301147 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663275653/1250000000 : ℝ), (1354239701/2500000000 : ℝ), (-202109587/1000000000 : ℝ)] ![(43337718631331/100000000000000 : ℝ), (44535208150981/100000000000000 : ℝ), (3031768301147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663275653/1250000000 : ℝ)|^8459 ≤ (43337718631331/100000000000000 : ℝ)^6411
        have hw : |(663275653/1250000000 : ℝ)|=(663275653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354239701/2500000000 : ℝ)|^8459 ≤ (44535208150981/100000000000000 : ℝ)^6411
        have hw : |(1354239701/2500000000 : ℝ)|=(1354239701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202109587/1000000000 : ℝ)|^8459 ≤ (3031768301147/25000000000000 : ℝ)^6411
        have hw : |(-202109587/1000000000 : ℝ)|=(202109587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345933941/10000000000 : ℝ)*x 0 + (4526655041/10000000000 : ℝ)*x 1 + (4172244647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345933941/10000000000 : ℝ)^8459 ≤ (16650927750293/50000000000000 : ℝ)^6411 := by
    have hnat : (4345933941 : ℕ)^8459*50000000000000^6411 ≤ 16650927750293^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345933941 10000000000 16650927750293 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526655041/10000000000 : ℝ)^8459 ≤ (702821698281/2000000000000 : ℝ)^6411 := by
    have hnat : (4526655041 : ℕ)^8459*2000000000000^6411 ≤ 702821698281^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526655041 10000000000 702821698281 2000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172244647/10000000000 : ℝ)^8459 ≤ (6311411914361/20000000000000 : ℝ)^6411 := by
    have hnat : (4172244647 : ℕ)^8459*20000000000000^6411 ≤ 6311411914361^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172244647 10000000000 6311411914361 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345933941/10000000000 : ℝ), (4526655041/10000000000 : ℝ), (4172244647/10000000000 : ℝ)] ![(16650927750293/50000000000000 : ℝ), (702821698281/2000000000000 : ℝ), (6311411914361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345933941/10000000000 : ℝ)|^8459 ≤ (16650927750293/50000000000000 : ℝ)^6411
        have hw : |(4345933941/10000000000 : ℝ)|=(4345933941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526655041/10000000000 : ℝ)|^8459 ≤ (702821698281/2000000000000 : ℝ)^6411
        have hw : |(4526655041/10000000000 : ℝ)|=(4526655041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172244647/10000000000 : ℝ)|^8459 ≤ (6311411914361/20000000000000 : ℝ)^6411
        have hw : |(4172244647/10000000000 : ℝ)|=(4172244647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_8 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-22679989/2500000000 : ℝ)*x 0 + (118090863/200000000 : ℝ)*x 1 + (5904551799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22679989/2500000000 : ℝ)^8459 ≤ (50492756649/25000000000000 : ℝ)^6411 := by
    have hnat : (22679989 : ℕ)^8459*25000000000000^6411 ≤ 50492756649^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22679989 2500000000 50492756649 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118090863/200000000 : ℝ)^8459 ≤ (24949483130267/50000000000000 : ℝ)^6411 := by
    have hnat : (118090863 : ℕ)^8459*50000000000000^6411 ≤ 24949483130267^6411*200000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118090863 200000000 24949483130267 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5904551799/10000000000 : ℝ)^8459 ≤ (24949531351077/50000000000000 : ℝ)^6411 := by
    have hnat : (5904551799 : ℕ)^8459*50000000000000^6411 ≤ 24949531351077^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904551799 10000000000 24949531351077 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22679989/2500000000 : ℝ), (118090863/200000000 : ℝ), (5904551799/10000000000 : ℝ)] ![(50492756649/25000000000000 : ℝ), (24949483130267/50000000000000 : ℝ), (24949531351077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22679989/2500000000 : ℝ)|^8459 ≤ (50492756649/25000000000000 : ℝ)^6411
        have hw : |(-22679989/2500000000 : ℝ)|=(22679989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118090863/200000000 : ℝ)|^8459 ≤ (24949483130267/50000000000000 : ℝ)^6411
        have hw : |(118090863/200000000 : ℝ)|=(118090863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5904551799/10000000000 : ℝ)|^8459 ≤ (24949531351077/50000000000000 : ℝ)^6411
        have hw : |(5904551799/10000000000 : ℝ)|=(5904551799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_9 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (980099129/10000000000 : ℝ)*x 0 + (-2186222369/5000000000 : ℝ)*x 1 + (6940560071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980099129/10000000000 : ℝ)^8459 ≤ (2333459449519/50000000000000 : ℝ)^6411 := by
    have hnat : (980099129 : ℕ)^8459*50000000000000^6411 ≤ 2333459449519^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980099129 10000000000 2333459449519 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186222369/5000000000 : ℝ)^8459 ≤ (16785078687839/50000000000000 : ℝ)^6411 := by
    have hnat : (2186222369 : ℕ)^8459*50000000000000^6411 ≤ 16785078687839^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186222369 5000000000 16785078687839 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6940560071/10000000000 : ℝ)^8459 ≤ (61762923717271/100000000000000 : ℝ)^6411 := by
    have hnat : (6940560071 : ℕ)^8459*100000000000000^6411 ≤ 61762923717271^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6940560071 10000000000 61762923717271 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980099129/10000000000 : ℝ), (-2186222369/5000000000 : ℝ), (6940560071/10000000000 : ℝ)] ![(2333459449519/50000000000000 : ℝ), (16785078687839/50000000000000 : ℝ), (61762923717271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980099129/10000000000 : ℝ)|^8459 ≤ (2333459449519/50000000000000 : ℝ)^6411
        have hw : |(980099129/10000000000 : ℝ)|=(980099129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186222369/5000000000 : ℝ)|^8459 ≤ (16785078687839/50000000000000 : ℝ)^6411
        have hw : |(-2186222369/5000000000 : ℝ)|=(2186222369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6940560071/10000000000 : ℝ)|^8459 ≤ (61762923717271/100000000000000 : ℝ)^6411
        have hw : |(6940560071/10000000000 : ℝ)|=(6940560071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s3_10 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (980090131/10000000000 : ℝ)*x 0 + (6940539821/10000000000 : ℝ)*x 1 + (-4372473789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980090131/10000000000 : ℝ)^8459 ≤ (1166715591613/25000000000000 : ℝ)^6411 := by
    have hnat : (980090131 : ℕ)^8459*25000000000000^6411 ≤ 1166715591613^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980090131 10000000000 1166715591613 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6940539821/10000000000 : ℝ)^8459 ≤ (61762685950367/100000000000000 : ℝ)^6411 := by
    have hnat : (6940539821 : ℕ)^8459*100000000000000^6411 ≤ 61762685950367^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6940539821 10000000000 61762685950367 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4372473789/10000000000 : ℝ)^8459 ≤ (1049076614729/3125000000000 : ℝ)^6411 := by
    have hnat : (4372473789 : ℕ)^8459*3125000000000^6411 ≤ 1049076614729^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372473789 10000000000 1049076614729 3125000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980090131/10000000000 : ℝ), (6940539821/10000000000 : ℝ), (-4372473789/10000000000 : ℝ)] ![(1166715591613/25000000000000 : ℝ), (61762685950367/100000000000000 : ℝ), (1049076614729/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980090131/10000000000 : ℝ)|^8459 ≤ (1166715591613/25000000000000 : ℝ)^6411
        have hw : |(980090131/10000000000 : ℝ)|=(980090131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6940539821/10000000000 : ℝ)|^8459 ≤ (61762685950367/100000000000000 : ℝ)^6411
        have hw : |(6940539821/10000000000 : ℝ)|=(6940539821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4372473789/10000000000 : ℝ)|^8459 ≤ (1049076614729/3125000000000 : ℝ)^6411
        have hw : |(-4372473789/10000000000 : ℝ)|=(4372473789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2743/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16161/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2399/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16161/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2399/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16161/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2399/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16161/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2399/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16161/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2399/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16161/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2399/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (2399/25000 : ℝ) ^ (4229/1024 : ℝ) ≤ (6253915005071427/100000000000000000000 : ℝ) := by
    have hpowers : (2399/25000 : ℝ)^4229 ≤ (6253915005071427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2399 : ℕ)^4229*100000000000000000000^1024 ≤ 6253915005071427^1024*25000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2399 25000 6253915005071427 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2399/25000 : ℝ)) (X := (6253915005071427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16161/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (26917613500026353/50000000000000000000 : ℝ) := by
    have hpowers : (16161/100000 : ℝ)^4229 ≤ (26917613500026353/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16161 : ℕ)^4229*50000000000000000000^1024 ≤ 26917613500026353^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16161 100000 26917613500026353 50000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16161/100000 : ℝ)) (X := (26917613500026353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006253915005071427/50000000000000000000 : ℝ) ≤ (10000302847267089/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50006253915005071427/50000000000000000000 : ℝ)^1024 ≤ (10000302847267089/10000000000000000 : ℝ)^4229 := by
      have hnat : (50006253915005071427 : ℕ)^1024*10000000000000000^4229 ≤ 10000302847267089^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006253915005071427 50000000000000000000 10000302847267089 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000302847267089/10000000000000000 : ℝ)) (X := (50006253915005071427/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060089142005124133/100000000000000000000 : ℝ) ≤ (500072732650611/500000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (100060089142005124133/100000000000000000000 : ℝ)^1024 ≤ (500072732650611/500000000000000 : ℝ)^4229 := by
      have hnat : (100060089142005124133 : ℕ)^1024*500000000000000^4229 ≤ 500072732650611^4229*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060089142005124133 100000000000000000000 500072732650611 500000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500072732650611/500000000000000 : ℝ)) (X := (100060089142005124133/100000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25026917613500026353/25000000000000000000 : ℝ) ≤ (10002606458757351/10000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25026917613500026353/25000000000000000000 : ℝ)^1024 ≤ (10002606458757351/10000000000000000 : ℝ)^4229 := by
      have hnat : (25026917613500026353 : ℕ)^1024*10000000000000000^4229 ≤ 10002606458757351^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026917613500026353 25000000000000000000 10002606458757351 10000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002606458757351/10000000000000000 : ℝ)) (X := (25026917613500026353/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6253915005071427/100000000000000000000 : ℝ) ≤ ((65629882736447885133/65650000000000000000 : ℝ)+2*(1151805745131/656500000000000 : ℝ)*(2399/25000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (65629882736447885133/65650000000000000000 : ℝ)+2*(1151805745131/656500000000000 : ℝ)*(2399/25000 : ℝ)=(10000302847267089/10000000000000000 : ℝ) by norm_num, show 1+2*(6253915005071427/100000000000000000000 : ℝ)=(50006253915005071427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26917613500026353/50000000000000000000 : ℝ)+(6253915005071427/100000000000000000000 : ℝ) ≤ ((65629882736447885133/65650000000000000000 : ℝ)+(1151805745131/656500000000000 : ℝ)*((16161/100000 : ℝ)+(2399/25000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (65629882736447885133/65650000000000000000 : ℝ)+(1151805745131/656500000000000 : ℝ)*((16161/100000 : ℝ)+(2399/25000 : ℝ))=(500072732650611/500000000000000 : ℝ) by norm_num, show 1+(26917613500026353/50000000000000000000 : ℝ)+(6253915005071427/100000000000000000000 : ℝ)=(100060089142005124133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26917613500026353/50000000000000000000 : ℝ) ≤ ((65629882736447885133/65650000000000000000 : ℝ)+2*(1151805745131/656500000000000 : ℝ)*(16161/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (65629882736447885133/65650000000000000000 : ℝ)+2*(1151805745131/656500000000000 : ℝ)*(16161/100000 : ℝ)=(10002606458757351/10000000000000000 : ℝ) by norm_num, show 1+2*(26917613500026353/50000000000000000000 : ℝ)=(25026917613500026353/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (65629882736447885133/65650000000000000000 : ℝ)*(X 1 0+X 2 0)+(1151805745131/656500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2399/25000 : ℝ)) (hi := (16161/100000 : ℝ)) (c := (65629882736447885133/65650000000000000000 : ℝ)) (alpha := (1151805745131/656500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (65629882736447885133/65650000000000000000 : ℝ)*(X 0 1+X 2 1)+(1151805745131/656500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2399/25000 : ℝ)) (hi := (16161/100000 : ℝ)) (c := (65629882736447885133/65650000000000000000 : ℝ)) (alpha := (1151805745131/656500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (65629882736447885133/65650000000000000000 : ℝ)*(X 0 2+X 1 2)+(1151805745131/656500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2399/25000 : ℝ)) (hi := (16161/100000 : ℝ)) (c := (65629882736447885133/65650000000000000000 : ℝ)) (alpha := (1151805745131/656500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526577211/2500000000 : ℝ)*X 0 0+(216703581/400000000 : ℝ)*X 0 1+(1310606813/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350964513/10000000000 : ℝ)*X 1 0+(-2195627427/10000000000 : ℝ)*X 1 1+(5242427369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10701929/20000000 : ℝ)*X 2 0+(2621213919/5000000000 : ℝ)*X 2 1+(-274453353/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543238291/1250000000 : ℝ)*X 0 0+(4170959613/10000000000 : ℝ)*X 0 1+(181117367/400000000 : ℝ)*X 0 2+(543238291/1250000000 : ℝ)*X 1 0+(4170959613/10000000000 : ℝ)*X 1 1+(181117367/400000000 : ℝ)*X 1 2+(543238291/1250000000 : ℝ)*X 2 0+(4170959613/10000000000 : ℝ)*X 2 1+(181117367/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2106322727/10000000000 : ℝ)*X 0 0+(1048610903/2000000000 : ℝ)*X 0 1+(5416958523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061241181/2000000000 : ℝ)*X 1 0+(-2021095551/10000000000 : ℝ)*X 1 1+(5416958361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663275653/1250000000 : ℝ)*X 2 0+(1354239701/2500000000 : ℝ)*X 2 1+(-202109587/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345933941/10000000000 : ℝ)*X 0 0+(4526655041/10000000000 : ℝ)*X 0 1+(4172244647/10000000000 : ℝ)*X 0 2+(4345933941/10000000000 : ℝ)*X 1 0+(4526655041/10000000000 : ℝ)*X 1 1+(4172244647/10000000000 : ℝ)*X 1 2+(4345933941/10000000000 : ℝ)*X 2 0+(4526655041/10000000000 : ℝ)*X 2 1+(4172244647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-22679989/2500000000 : ℝ)*X 0 0+(118090863/200000000 : ℝ)*X 0 1+(5904551799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((980099129/10000000000 : ℝ)*X 1 0+(-2186222369/5000000000 : ℝ)*X 1 1+(6940560071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((980090131/10000000000 : ℝ)*X 2 0+(6940539821/10000000000 : ℝ)*X 2 1+(-4372473789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3086698041587749257390894201/820625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7555283/50000000000000 : ℝ)*(base8) + (140426329/100000000000000 : ℝ)*(lower2) + (55669641/50000000000000 : ℝ)*(lower3) + (81555353/100000000000000 : ℝ)*(lower4) + (2127591211260399/50000000000000 : ℝ)*(major0) + (2127591211260399/50000000000000 : ℝ)*(major1) + (2127591211260399/50000000000000 : ℝ)*(major2) + (5709011373324313/100000000000000 : ℝ)*(sp0) + (5709022048771121/100000000000000 : ℝ)*(sp1) + (178407401873069/3125000000000 : ℝ)*(sp2) + (175082768965679/6250000000000 : ℝ)*(sp3) + (25471503329/100000000000000 : ℝ)*(sp4) + (14811167087/100000000000000 : ℝ)*(sp5) + (71125451/2000000000000 : ℝ)*(sp7) + (1400663929861707/50000000000000 : ℝ)*(f.failure) + (178407401873069/3125000000000 : ℝ)*(f.sum) + (195939111666263/32825000000000000000000000000 : ℝ)*base65 + (8234331294537257841/252500000000000000000000000000000 : ℝ)*base68 + (290286397414757841/252500000000000000000000000000000 : ℝ)*base70 + (3081559453557257841/252500000000000000000000000000000 : ℝ)*base72 + (5496520463961/4103125000000000000000000000 : ℝ)*base73 + (2735767610947257841/252500000000000000000000000000000 : ℝ)*base76 + (1339630152962742159/252500000000000000000000000000000 : ℝ)*base77 + (1439918011897257841/252500000000000000000000000000000 : ℝ)*base80 + (303827500167/512890625000000000000000000 : ℝ)*base81 + (2818371/1000000000000000000000 : ℝ)*base89 + (2818371/1000000000000000000000 : ℝ)*base91 + (2818371/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12487976837643090916779/6565000000000000000000000000 : ℝ) := by norm_num
    linear_combination (509700507/100000000000000 : ℝ)*(lower4) + (857189245020037/20000000000000 : ℝ)*(major0) + (857189245020037/20000000000000 : ℝ)*(major1) + (857189245020037/20000000000000 : ℝ)*(major2) + (13755875849/100000000000000 : ℝ)*(sp0) + (1250889213/20000000000000 : ℝ)*(sp1) + (3124314303/50000000000000 : ℝ)*(sp2) + (2875147780511051/50000000000000 : ℝ)*(sp4) + (5750304927035049/100000000000000 : ℝ)*(sp5) + (2875152329954811/50000000000000 : ℝ)*(sp6) + (2821580692311873/100000000000000 : ℝ)*(sp7) + (2377583703/100000000000000 : ℝ)*(sp8) + (513000539/100000000000000 : ℝ)*(sp9) + (785943427/100000000000000 : ℝ)*(sp10) + (2821580692311873/100000000000000 : ℝ)*(f.failure) + (5750311694481653/100000000000000 : ℝ)*(f.sum) + (1409642325109/820625000000000000000000000 : ℝ)*base65 + (349538029848453083/101000000000000000000000000000000 : ℝ)*base68 + (132951541572453083/101000000000000000000000000000000 : ℝ)*base70 + (137741960664453083/101000000000000000000000000000000 : ℝ)*base72 + (4726950368679/3282500000000000000000000000 : ℝ)*base74 + (742962681275546917/101000000000000000000000000000000 : ℝ)*base75 + (320991449891546917/101000000000000000000000000000000 : ℝ)*base77 + (200669996573546917/101000000000000000000000000000000 : ℝ)*base79 + (20200373724987/6565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/50000000000000 : ℝ)*base87 + (707369/2000000000000000000000 : ℝ)*base89 + (707369/2000000000000000000000 : ℝ)*base91 + (707369/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1266_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1266_s4_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-3373531/16000000 : ℝ)*x 0 + (5396537977/10000000000 : ℝ)*x 1 + (328879409/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3373531/16000000 : ℝ)^8459 ≤ (12823442103689/100000000000000 : ℝ)^6411 := by
    have hnat : (3373531 : ℕ)^8459*100000000000000^6411 ≤ 12823442103689^6411*16000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3373531 16000000 12823442103689 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396537977/10000000000 : ℝ)^8459 ≤ (8862764168309/20000000000000 : ℝ)^6411 := by
    have hnat : (5396537977 : ℕ)^8459*20000000000000^6411 ≤ 8862764168309^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396537977 10000000000 8862764168309 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328879409/625000000 : ℝ)^8459 ≤ (21431368516929/50000000000000 : ℝ)^6411 := by
    have hnat : (328879409 : ℕ)^8459*50000000000000^6411 ≤ 21431368516929^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328879409 625000000 21431368516929 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3373531/16000000 : ℝ), (5396537977/10000000000 : ℝ), (328879409/625000000 : ℝ)] ![(12823442103689/100000000000000 : ℝ), (8862764168309/20000000000000 : ℝ), (21431368516929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3373531/16000000 : ℝ)|^8459 ≤ (12823442103689/100000000000000 : ℝ)^6411
        have hw : |(-3373531/16000000 : ℝ)|=(3373531/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396537977/10000000000 : ℝ)|^8459 ≤ (8862764168309/20000000000000 : ℝ)^6411
        have hw : |(5396537977/10000000000 : ℝ)|=(5396537977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328879409/625000000 : ℝ)|^8459 ≤ (21431368516929/50000000000000 : ℝ)^6411
        have hw : |(328879409/625000000 : ℝ)|=(328879409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336411489/2500000000 : ℝ)*x 0 + (-544178749/2500000000 : ℝ)*x 1 + (657758813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336411489/2500000000 : ℝ)^8459 ≤ (547040662643/1250000000000 : ℝ)^6411 := by
    have hnat : (1336411489 : ℕ)^8459*1250000000000^6411 ≤ 547040662643^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336411489 2500000000 547040662643 1250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544178749/2500000000 : ℝ)^8459 ≤ (6687005185401/50000000000000 : ℝ)^6411 := by
    have hnat : (544178749 : ℕ)^8459*50000000000000^6411 ≤ 6687005185401^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544178749 2500000000 6687005185401 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657758813/1250000000 : ℝ)^8459 ≤ (42862736603949/100000000000000 : ℝ)^6411 := by
    have hnat : (657758813 : ℕ)^8459*100000000000000^6411 ≤ 42862736603949^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657758813 1250000000 42862736603949 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336411489/2500000000 : ℝ), (-544178749/2500000000 : ℝ), (657758813/1250000000 : ℝ)] ![(547040662643/1250000000000 : ℝ), (6687005185401/50000000000000 : ℝ), (42862736603949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336411489/2500000000 : ℝ)|^8459 ≤ (547040662643/1250000000000 : ℝ)^6411
        have hw : |(1336411489/2500000000 : ℝ)|=(1336411489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544178749/2500000000 : ℝ)|^8459 ≤ (6687005185401/50000000000000 : ℝ)^6411
        have hw : |(-544178749/2500000000 : ℝ)|=(544178749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657758813/1250000000 : ℝ)|^8459 ≤ (42862736603949/100000000000000 : ℝ)^6411
        have hw : |(657758813/1250000000 : ℝ)|=(657758813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345646049/10000000000 : ℝ)*x 0 + (5262070423/10000000000 : ℝ)*x 1 + (-2176714979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345646049/10000000000 : ℝ)^8459 ≤ (43763254016023/100000000000000 : ℝ)^6411 := by
    have hnat : (5345646049 : ℕ)^8459*100000000000000^6411 ≤ 43763254016023^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345646049 10000000000 43763254016023 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262070423/10000000000 : ℝ)^8459 ≤ (42862735733383/100000000000000 : ℝ)^6411 := by
    have hnat : (5262070423 : ℕ)^8459*100000000000000^6411 ≤ 42862735733383^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262070423 10000000000 42862735733383 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176714979/10000000000 : ℝ)^8459 ≤ (2674802046597/20000000000000 : ℝ)^6411 := by
    have hnat : (2176714979 : ℕ)^8459*20000000000000^6411 ≤ 2674802046597^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176714979 10000000000 2674802046597 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345646049/10000000000 : ℝ), (5262070423/10000000000 : ℝ), (-2176714979/10000000000 : ℝ)] ![(43763254016023/100000000000000 : ℝ), (42862735733383/100000000000000 : ℝ), (2674802046597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345646049/10000000000 : ℝ)|^8459 ≤ (43763254016023/100000000000000 : ℝ)^6411
        have hw : |(5345646049/10000000000 : ℝ)|=(5345646049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262070423/10000000000 : ℝ)|^8459 ≤ (42862735733383/100000000000000 : ℝ)^6411
        have hw : |(5262070423/10000000000 : ℝ)|=(5262070423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2176714979/10000000000 : ℝ)|^8459 ≤ (2674802046597/20000000000000 : ℝ)^6411
        have hw : |(-2176714979/10000000000 : ℝ)|=(2176714979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271699709/625000000 : ℝ)*x 0 + (4212262343/10000000000 : ℝ)*x 1 + (4486303811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271699709/625000000 : ℝ)^8459 ≤ (33314609680857/100000000000000 : ℝ)^6411 := by
    have hnat : (271699709 : ℕ)^8459*100000000000000^6411 ≤ 33314609680857^6411*625000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271699709 625000000 33314609680857 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212262343/10000000000 : ℝ)^8459 ≤ (1278281479839/4000000000000 : ℝ)^6411 := by
    have hnat : (4212262343 : ℕ)^8459*4000000000000^6411 ≤ 1278281479839^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212262343 10000000000 1278281479839 4000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486303811/10000000000 : ℝ)^8459 ≤ (34728353297339/100000000000000 : ℝ)^6411 := by
    have hnat : (4486303811 : ℕ)^8459*100000000000000^6411 ≤ 34728353297339^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486303811 10000000000 34728353297339 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271699709/625000000 : ℝ), (4212262343/10000000000 : ℝ), (4486303811/10000000000 : ℝ)] ![(33314609680857/100000000000000 : ℝ), (1278281479839/4000000000000 : ℝ), (34728353297339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271699709/625000000 : ℝ)|^8459 ≤ (33314609680857/100000000000000 : ℝ)^6411
        have hw : |(271699709/625000000 : ℝ)|=(271699709/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212262343/10000000000 : ℝ)|^8459 ≤ (1278281479839/4000000000000 : ℝ)^6411
        have hw : |(4212262343/10000000000 : ℝ)|=(4212262343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486303811/10000000000 : ℝ)|^8459 ≤ (34728353297339/100000000000000 : ℝ)^6411
        have hw : |(4486303811/10000000000 : ℝ)|=(4486303811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108463083/10000000000 : ℝ)*x 0 + (5262440899/10000000000 : ℝ)*x 1 + (539616599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108463083/10000000000 : ℝ)^8459 ≤ (12823491921547/100000000000000 : ℝ)^6411 := by
    have hnat : (2108463083 : ℕ)^8459*100000000000000^6411 ≤ 12823491921547^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108463083 10000000000 12823491921547 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262440899/10000000000 : ℝ)^8459 ≤ (1339584923491/3125000000000 : ℝ)^6411 := by
    have hnat : (5262440899 : ℕ)^8459*3125000000000^6411 ≤ 1339584923491^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262440899 10000000000 1339584923491 3125000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539616599/1000000000 : ℝ)^8459 ≤ (44309790515427/100000000000000 : ℝ)^6411 := by
    have hnat : (539616599 : ℕ)^8459*100000000000000^6411 ≤ 44309790515427^6411*1000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539616599 1000000000 44309790515427 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108463083/10000000000 : ℝ), (5262440899/10000000000 : ℝ), (539616599/1000000000 : ℝ)] ![(12823491921547/100000000000000 : ℝ), (1339584923491/3125000000000 : ℝ), (44309790515427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108463083/10000000000 : ℝ)|^8459 ≤ (12823491921547/100000000000000 : ℝ)^6411
        have hw : |(-2108463083/10000000000 : ℝ)|=(2108463083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262440899/10000000000 : ℝ)|^8459 ≤ (1339584923491/3125000000000 : ℝ)^6411
        have hw : |(5262440899/10000000000 : ℝ)|=(5262440899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539616599/1000000000 : ℝ)|^8459 ≤ (44309790515427/100000000000000 : ℝ)^6411
        have hw : |(539616599/1000000000 : ℝ)|=(539616599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311282367/10000000000 : ℝ)*x 0 + (-81704781/400000000 : ℝ)*x 1 + (2698083141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311282367/10000000000 : ℝ)^8459 ≤ (216962202551/500000000000 : ℝ)^6411 := by
    have hnat : (5311282367 : ℕ)^8459*500000000000^6411 ≤ 216962202551^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311282367 10000000000 216962202551 500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81704781/400000000 : ℝ)^8459 ≤ (6148882900929/50000000000000 : ℝ)^6411 := by
    have hnat : (81704781 : ℕ)^8459*50000000000000^6411 ≤ 6148882900929^6411*400000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81704781 400000000 6148882900929 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698083141/5000000000 : ℝ)^8459 ≤ (11077448419773/25000000000000 : ℝ)^6411 := by
    have hnat : (2698083141 : ℕ)^8459*25000000000000^6411 ≤ 11077448419773^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698083141 5000000000 11077448419773 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311282367/10000000000 : ℝ), (-81704781/400000000 : ℝ), (2698083141/5000000000 : ℝ)] ![(216962202551/500000000000 : ℝ), (6148882900929/50000000000000 : ℝ), (11077448419773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311282367/10000000000 : ℝ)|^8459 ≤ (216962202551/500000000000 : ℝ)^6411
        have hw : |(5311282367/10000000000 : ℝ)|=(5311282367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81704781/400000000 : ℝ)|^8459 ≤ (6148882900929/50000000000000 : ℝ)^6411
        have hw : |(-81704781/400000000 : ℝ)|=(81704781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698083141/5000000000 : ℝ)|^8459 ≤ (11077448419773/25000000000000 : ℝ)^6411
        have hw : |(2698083141/5000000000 : ℝ)|=(2698083141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327820571/2500000000 : ℝ)*x 0 + (2698083377/5000000000 : ℝ)*x 1 + (-1021309497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327820571/2500000000 : ℝ)^8459 ≤ (21696219807741/50000000000000 : ℝ)^6411 := by
    have hnat : (1327820571 : ℕ)^8459*50000000000000^6411 ≤ 21696219807741^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327820571 2500000000 21696219807741 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698083377/5000000000 : ℝ)^8459 ≤ (22154899396481/50000000000000 : ℝ)^6411 := by
    have hnat : (2698083377 : ℕ)^8459*50000000000000^6411 ≤ 22154899396481^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698083377 5000000000 22154899396481 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021309497/5000000000 : ℝ)^8459 ≤ (768610098979/6250000000000 : ℝ)^6411 := by
    have hnat : (1021309497 : ℕ)^8459*6250000000000^6411 ≤ 768610098979^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021309497 5000000000 768610098979 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327820571/2500000000 : ℝ), (2698083377/5000000000 : ℝ), (-1021309497/5000000000 : ℝ)] ![(21696219807741/50000000000000 : ℝ), (22154899396481/50000000000000 : ℝ), (768610098979/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327820571/2500000000 : ℝ)|^8459 ≤ (21696219807741/50000000000000 : ℝ)^6411
        have hw : |(1327820571/2500000000 : ℝ)|=(1327820571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698083377/5000000000 : ℝ)|^8459 ≤ (22154899396481/50000000000000 : ℝ)^6411
        have hw : |(2698083377/5000000000 : ℝ)|=(2698083377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021309497/5000000000 : ℝ)|^8459 ≤ (768610098979/6250000000000 : ℝ)^6411
        have hw : |(-1021309497/5000000000 : ℝ)|=(1021309497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s4_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347207499/10000000000 : ℝ)*x 0 + (2242774821/5000000000 : ℝ)*x 1 + (1053254883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347207499/10000000000 : ℝ)^8459 ≤ (3331473258711/10000000000000 : ℝ)^6411 := by
    have hnat : (4347207499 : ℕ)^8459*10000000000000^6411 ≤ 3331473258711^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347207499 10000000000 3331473258711 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242774821/5000000000 : ℝ)^8459 ≤ (8680162636963/25000000000000 : ℝ)^6411 := by
    have hnat : (2242774821 : ℕ)^8459*25000000000000^6411 ≤ 8680162636963^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242774821 5000000000 8680162636963 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053254883/2500000000 : ℝ)^8459 ≤ (998894276707/3125000000000 : ℝ)^6411 := by
    have hnat : (1053254883 : ℕ)^8459*3125000000000^6411 ≤ 998894276707^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053254883 2500000000 998894276707 3125000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347207499/10000000000 : ℝ), (2242774821/5000000000 : ℝ), (1053254883/2500000000 : ℝ)] ![(3331473258711/10000000000000 : ℝ), (8680162636963/25000000000000 : ℝ), (998894276707/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347207499/10000000000 : ℝ)|^8459 ≤ (3331473258711/10000000000000 : ℝ)^6411
        have hw : |(4347207499/10000000000 : ℝ)|=(4347207499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242774821/5000000000 : ℝ)|^8459 ≤ (8680162636963/25000000000000 : ℝ)^6411
        have hw : |(2242774821/5000000000 : ℝ)|=(2242774821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053254883/2500000000 : ℝ)|^8459 ≤ (998894276707/3125000000000 : ℝ)^6411
        have hw : |(1053254883/2500000000 : ℝ)|=(1053254883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2743/25000 : ℝ) ^ (4229/1024 : ℝ) ≤ (10876591459216029/100000000000000000000 : ℝ) := by
    have hpowers : (2743/25000 : ℝ)^4229 ≤ (10876591459216029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2743 : ℕ)^4229*100000000000000000000^1024 ≤ 10876591459216029^1024*25000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2743 25000 10876591459216029 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2743/25000 : ℝ)) (X := (10876591459216029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (9046781151071077/25000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^4229 ≤ (9046781151071077/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14679 : ℕ)^4229*25000000000000000000^1024 ≤ 9046781151071077^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 9046781151071077 25000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (9046781151071077/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010876591459216029/50000000000000000000 : ℝ) ≤ (5000263341492101/5000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50010876591459216029/50000000000000000000 : ℝ)^1024 ≤ (5000263341492101/5000000000000000 : ℝ)^4229 := by
      have hnat : (50010876591459216029 : ℕ)^1024*5000000000000000^4229 ≤ 5000263341492101^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010876591459216029 50000000000000000000 5000263341492101 5000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000263341492101/5000000000000000 : ℝ)) (X := (50010876591459216029/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047063716063500337/100000000000000000000 : ℝ) ≤ (400045575457913/400000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (100047063716063500337/100000000000000000000 : ℝ)^1024 ≤ (400045575457913/400000000000000 : ℝ)^4229 := by
      have hnat : (100047063716063500337 : ℕ)^1024*400000000000000^4229 ≤ 400045575457913^4229*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047063716063500337 100000000000000000000 400045575457913 400000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400045575457913/400000000000000 : ℝ)) (X := (100047063716063500337/100000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509046781151071077/12500000000000000000 : ℝ) ≤ (1250219011238931/1250000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (12509046781151071077/12500000000000000000 : ℝ)^1024 ≤ (1250219011238931/1250000000000000 : ℝ)^4229 := by
      have hnat : (12509046781151071077 : ℕ)^1024*1250000000000000^4229 ≤ 1250219011238931^4229*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509046781151071077 12500000000000000000 1250219011238931 1250000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250219011238931/1250000000000000 : ℝ)) (X := (12509046781151071077/12500000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10876591459216029/100000000000000000000 : ℝ) ≤ ((18529253624508346851/18535000000000000000 : ℝ)+2*(612703463623/370700000000000 : ℝ)*(2743/25000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (18529253624508346851/18535000000000000000 : ℝ)+2*(612703463623/370700000000000 : ℝ)*(2743/25000 : ℝ)=(5000263341492101/5000000000000000 : ℝ) by norm_num, show 1+2*(10876591459216029/100000000000000000000 : ℝ)=(50010876591459216029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9046781151071077/25000000000000000000 : ℝ)+(10876591459216029/100000000000000000000 : ℝ) ≤ ((18529253624508346851/18535000000000000000 : ℝ)+(612703463623/370700000000000 : ℝ)*((14679/100000 : ℝ)+(2743/25000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (18529253624508346851/18535000000000000000 : ℝ)+(612703463623/370700000000000 : ℝ)*((14679/100000 : ℝ)+(2743/25000 : ℝ))=(400045575457913/400000000000000 : ℝ) by norm_num, show 1+(9046781151071077/25000000000000000000 : ℝ)+(10876591459216029/100000000000000000000 : ℝ)=(100047063716063500337/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9046781151071077/25000000000000000000 : ℝ) ≤ ((18529253624508346851/18535000000000000000 : ℝ)+2*(612703463623/370700000000000 : ℝ)*(14679/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (18529253624508346851/18535000000000000000 : ℝ)+2*(612703463623/370700000000000 : ℝ)*(14679/100000 : ℝ)=(1250219011238931/1250000000000000 : ℝ) by norm_num, show 1+2*(9046781151071077/25000000000000000000 : ℝ)=(12509046781151071077/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18529253624508346851/18535000000000000000 : ℝ)*(X 1 0+X 2 0)+(612703463623/370700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (18529253624508346851/18535000000000000000 : ℝ)) (alpha := (612703463623/370700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18529253624508346851/18535000000000000000 : ℝ)*(X 0 1+X 2 1)+(612703463623/370700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (18529253624508346851/18535000000000000000 : ℝ)) (alpha := (612703463623/370700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18529253624508346851/18535000000000000000 : ℝ)*(X 0 2+X 1 2)+(612703463623/370700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (18529253624508346851/18535000000000000000 : ℝ)) (alpha := (612703463623/370700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3373531/16000000 : ℝ)*X 0 0+(5396537977/10000000000 : ℝ)*X 0 1+(328879409/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336411489/2500000000 : ℝ)*X 1 0+(-544178749/2500000000 : ℝ)*X 1 1+(657758813/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345646049/10000000000 : ℝ)*X 2 0+(5262070423/10000000000 : ℝ)*X 2 1+(-2176714979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271699709/625000000 : ℝ)*X 0 0+(4212262343/10000000000 : ℝ)*X 0 1+(4486303811/10000000000 : ℝ)*X 0 2+(271699709/625000000 : ℝ)*X 1 0+(4212262343/10000000000 : ℝ)*X 1 1+(4486303811/10000000000 : ℝ)*X 1 2+(271699709/625000000 : ℝ)*X 2 0+(4212262343/10000000000 : ℝ)*X 2 1+(4486303811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108463083/10000000000 : ℝ)*X 0 0+(5262440899/10000000000 : ℝ)*X 0 1+(539616599/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311282367/10000000000 : ℝ)*X 1 0+(-81704781/400000000 : ℝ)*X 1 1+(2698083141/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327820571/2500000000 : ℝ)*X 2 0+(2698083377/5000000000 : ℝ)*X 2 1+(-1021309497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347207499/10000000000 : ℝ)*X 0 0+(2242774821/5000000000 : ℝ)*X 0 1+(1053254883/2500000000 : ℝ)*X 0 2+(4347207499/10000000000 : ℝ)*X 1 0+(2242774821/5000000000 : ℝ)*X 1 1+(1053254883/2500000000 : ℝ)*X 1 2+(4347207499/10000000000 : ℝ)*X 2 0+(2242774821/5000000000 : ℝ)*X 2 1+(1053254883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (215479089573569416438227/18535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486085823/25000000000000 : ℝ)*(base19) + (2060765917/100000000000000 : ℝ)*(base23) + (6927227/100000000000000 : ℝ)*(lower2) + (49035019/25000000000000 : ℝ)*(upper3) + (4711971/2000000000000 : ℝ)*(upper5) + (5542989824110433/100000000000000 : ℝ)*(major0) + (5542989824110433/100000000000000 : ℝ)*(major1) + (5542989824110433/100000000000000 : ℝ)*(major2) + (7436793180367619/100000000000000 : ℝ)*(sp0) + (7436843089290879/100000000000000 : ℝ)*(sp1) + (3718421486434127/50000000000000 : ℝ)*(sp2) + (145964338236957/4000000000000 : ℝ)*(sp3) + (51853266553/100000000000000 : ℝ)*(sp4) + (2577114529/10000000000000 : ℝ)*(sp7) + (729826845413843/20000000000000 : ℝ)*(f.failure) + (7436845033634171/100000000000000 : ℝ)*(f.sum) + (58374967189249/18535000000000000000000000000 : ℝ)*base65 + (531895754372523047/168500000000000000000000000000000 : ℝ)*base68 + (1588149680748523047/168500000000000000000000000000000 : ℝ)*base70 + (660715667299023047/168500000000000000000000000000000 : ℝ)*base72 + (3218921209363/9267500000000000000000000000 : ℝ)*base74 + (4827035260266476953/168500000000000000000000000000000 : ℝ)*base75 + (694261391643976953/168500000000000000000000000000000 : ℝ)*base77 + (3033811345485476953/168500000000000000000000000000000 : ℝ)*base79 + (44441921755089/4633750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1120779/400000000000000000000 : ℝ)*base89 + (1120779/400000000000000000000 : ℝ)*base91 + (1120779/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150685494926402530352560773/14480468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (116747249/12500000000000 : ℝ)*(base19) + (1542638121/100000000000000 : ℝ)*(base23) + (36865973/20000000000000 : ℝ)*(upper2) + (531038083/100000000000000 : ℝ)*(upper3) + (13829507/100000000000000 : ℝ)*(upper5) + (174177028481491/3125000000000 : ℝ)*(major0) + (174177028481491/3125000000000 : ℝ)*(major1) + (174177028481491/3125000000000 : ℝ)*(major2) + (8748036597/100000000000000 : ℝ)*(sp1) + (33621971333/50000000000000 : ℝ)*(sp2) + (7478000820502611/100000000000000 : ℝ)*(sp4) + (3738995569244011/50000000000000 : ℝ)*(sp5) + (233685376060057/3125000000000 : ℝ)*(sp6) + (1834664327721069/50000000000000 : ℝ)*(sp7) + (1834664327721069/50000000000000 : ℝ)*(f.failure) + (7478000820502611/100000000000000 : ℝ)*(f.sum) + (14124820006139/18535000000000000000000000000 : ℝ)*base66 + (19583849334593203/2632812500000000000000000000000 : ℝ)*base67 + (97200601500766719/5265625000000000000000000000000 : ℝ)*base70 + (29314128110047969/5265625000000000000000000000000 : ℝ)*base72 + (5389564021807/9267500000000000000000000000 : ℝ)*base74 + (137109348392547969/5265625000000000000000000000000 : ℝ)*base76 + (74362776054235469/5265625000000000000000000000000 : ℝ)*base78 + (54073459882766719/5265625000000000000000000000000 : ℝ)*base80 + (32097052476267/9267500000000000000000000000 : ℝ)*base82 + (9115957/1000000000000000000000 : ℝ)*base89 + (9115957/1000000000000000000000 : ℝ)*base91 + (9115957/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1266_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1266_s5_0 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-65902183/312500000 : ℝ)*x 0 + (2695920123/5000000000 : ℝ)*x 1 + (5266496681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65902183/312500000 : ℝ)^8459 ≤ (12826756289079/100000000000000 : ℝ)^6411 := by
    have hnat : (65902183 : ℕ)^8459*100000000000000^6411 ≤ 12826756289079^6411*312500000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65902183 312500000 12826756289079 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695920123/5000000000 : ℝ)^8459 ≤ (2766433086047/6250000000000 : ℝ)^6411 := by
    have hnat : (2695920123 : ℕ)^8459*6250000000000^6411 ≤ 2766433086047^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695920123 5000000000 2766433086047 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266496681/10000000000 : ℝ)^8459 ≤ (42910314320157/100000000000000 : ℝ)^6411 := by
    have hnat : (5266496681 : ℕ)^8459*100000000000000^6411 ≤ 42910314320157^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266496681 10000000000 42910314320157 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65902183/312500000 : ℝ), (2695920123/5000000000 : ℝ), (5266496681/10000000000 : ℝ)] ![(12826756289079/100000000000000 : ℝ), (2766433086047/6250000000000 : ℝ), (42910314320157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65902183/312500000 : ℝ)|^8459 ≤ (12826756289079/100000000000000 : ℝ)^6411
        have hw : |(-65902183/312500000 : ℝ)|=(65902183/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695920123/5000000000 : ℝ)|^8459 ≤ (2766433086047/6250000000000 : ℝ)^6411
        have hw : |(2695920123/5000000000 : ℝ)|=(2695920123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266496681/10000000000 : ℝ)|^8459 ≤ (42910314320157/100000000000000 : ℝ)^6411
        have hw : |(5266496681/10000000000 : ℝ)|=(5266496681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_1 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672227449/5000000000 : ℝ)*x 0 + (-543107941/2500000000 : ℝ)*x 1 + (1316624177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672227449/5000000000 : ℝ)^8459 ≤ (21875193852927/50000000000000 : ℝ)^6411 := by
    have hnat : (2672227449 : ℕ)^8459*50000000000000^6411 ≤ 21875193852927^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672227449 5000000000 21875193852927 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543107941/2500000000 : ℝ)^8459 ≤ (833706104641/6250000000000 : ℝ)^6411 := by
    have hnat : (543107941 : ℕ)^8459*6250000000000^6411 ≤ 833706104641^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543107941 2500000000 833706104641 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316624177/2500000000 : ℝ)^8459 ≤ (42910314610423/100000000000000 : ℝ)^6411 := by
    have hnat : (1316624177 : ℕ)^8459*100000000000000^6411 ≤ 42910314610423^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316624177 2500000000 42910314610423 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672227449/5000000000 : ℝ), (-543107941/2500000000 : ℝ), (1316624177/2500000000 : ℝ)] ![(21875193852927/50000000000000 : ℝ), (833706104641/6250000000000 : ℝ), (42910314610423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672227449/5000000000 : ℝ)|^8459 ≤ (21875193852927/50000000000000 : ℝ)^6411
        have hw : |(2672227449/5000000000 : ℝ)|=(2672227449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543107941/2500000000 : ℝ)|^8459 ≤ (833706104641/6250000000000 : ℝ)^6411
        have hw : |(-543107941/2500000000 : ℝ)|=(543107941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316624177/2500000000 : ℝ)|^8459 ≤ (42910314610423/100000000000000 : ℝ)^6411
        have hw : |(1316624177/2500000000 : ℝ)|=(1316624177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_2 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068890951/2000000000 : ℝ)*x 0 + (1316624177/2500000000 : ℝ)*x 1 + (-1086215977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068890951/2000000000 : ℝ)^8459 ≤ (10937596540321/25000000000000 : ℝ)^6411 := by
    have hnat : (1068890951 : ℕ)^8459*25000000000000^6411 ≤ 10937596540321^6411*2000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068890951 2000000000 10937596540321 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316624177/2500000000 : ℝ)^8459 ≤ (42910314610423/100000000000000 : ℝ)^6411 := by
    have hnat : (1316624177 : ℕ)^8459*100000000000000^6411 ≤ 42910314610423^6411*2500000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316624177 2500000000 42910314610423 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086215977/5000000000 : ℝ)^8459 ≤ (13339299213593/100000000000000 : ℝ)^6411 := by
    have hnat : (1086215977 : ℕ)^8459*100000000000000^6411 ≤ 13339299213593^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086215977 5000000000 13339299213593 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068890951/2000000000 : ℝ), (1316624177/2500000000 : ℝ), (-1086215977/5000000000 : ℝ)] ![(10937596540321/25000000000000 : ℝ), (42910314610423/100000000000000 : ℝ), (13339299213593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068890951/2000000000 : ℝ)|^8459 ≤ (10937596540321/25000000000000 : ℝ)^6411
        have hw : |(1068890951/2000000000 : ℝ)|=(1068890951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316624177/2500000000 : ℝ)|^8459 ≤ (42910314610423/100000000000000 : ℝ)^6411
        have hw : |(1316624177/2500000000 : ℝ)|=(1316624177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086215977/5000000000 : ℝ)|^8459 ≤ (13339299213593/100000000000000 : ℝ)^6411
        have hw : |(-1086215977/5000000000 : ℝ)|=(1086215977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_3 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173719117/5000000000 : ℝ)*x 0 + (4221528491/10000000000 : ℝ)*x 1 + (4476975621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173719117/5000000000 : ℝ)^8459 ≤ (16658532851653/50000000000000 : ℝ)^6411 := by
    have hnat : (2173719117 : ℕ)^8459*50000000000000^6411 ≤ 16658532851653^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173719117 5000000000 16658532851653 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221528491/10000000000 : ℝ)^8459 ≤ (2003114119047/6250000000000 : ℝ)^6411 := by
    have hnat : (4221528491 : ℕ)^8459*6250000000000^6411 ≤ 2003114119047^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221528491 10000000000 2003114119047 6250000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476975621/10000000000 : ℝ)^8459 ≤ (34633108378511/100000000000000 : ℝ)^6411 := by
    have hnat : (4476975621 : ℕ)^8459*100000000000000^6411 ≤ 34633108378511^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476975621 10000000000 34633108378511 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173719117/5000000000 : ℝ), (4221528491/10000000000 : ℝ), (4476975621/10000000000 : ℝ)] ![(16658532851653/50000000000000 : ℝ), (2003114119047/6250000000000 : ℝ), (34633108378511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173719117/5000000000 : ℝ)|^8459 ≤ (16658532851653/50000000000000 : ℝ)^6411
        have hw : |(2173719117/5000000000 : ℝ)|=(2173719117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221528491/10000000000 : ℝ)|^8459 ≤ (2003114119047/6250000000000 : ℝ)^6411
        have hw : |(4221528491/10000000000 : ℝ)|=(4221528491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476975621/10000000000 : ℝ)|^8459 ≤ (34633108378511/100000000000000 : ℝ)^6411
        have hw : |(4476975621/10000000000 : ℝ)|=(4476975621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_4 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108874501/10000000000 : ℝ)*x 0 + (5266818481/10000000000 : ℝ)*x 1 + (5391517407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108874501/10000000000 : ℝ)^8459 ≤ (200418649477/1562500000000 : ℝ)^6411 := by
    have hnat : (2108874501 : ℕ)^8459*1562500000000^6411 ≤ 200418649477^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108874501 10000000000 200418649477 1562500000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266818481/10000000000 : ℝ)^8459 ≤ (5364221737549/12500000000000 : ℝ)^6411 := by
    have hnat : (5266818481 : ℕ)^8459*12500000000000^6411 ≤ 5364221737549^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266818481 10000000000 5364221737549 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391517407/10000000000 : ℝ)^8459 ≤ (44259432516919/100000000000000 : ℝ)^6411 := by
    have hnat : (5391517407 : ℕ)^8459*100000000000000^6411 ≤ 44259432516919^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391517407 10000000000 44259432516919 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108874501/10000000000 : ℝ), (5266818481/10000000000 : ℝ), (5391517407/10000000000 : ℝ)] ![(200418649477/1562500000000 : ℝ), (5364221737549/12500000000000 : ℝ), (44259432516919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108874501/10000000000 : ℝ)|^8459 ≤ (200418649477/1562500000000 : ℝ)^6411
        have hw : |(-2108874501/10000000000 : ℝ)|=(2108874501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266818481/10000000000 : ℝ)|^8459 ≤ (5364221737549/12500000000000 : ℝ)^6411
        have hw : |(5266818481/10000000000 : ℝ)|=(5266818481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391517407/10000000000 : ℝ)|^8459 ≤ (44259432516919/100000000000000 : ℝ)^6411
        have hw : |(5391517407/10000000000 : ℝ)|=(5391517407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_5 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312421941/10000000000 : ℝ)*x 0 + (-1023705461/5000000000 : ℝ)*x 1 + (5391517403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312421941/10000000000 : ℝ)^8459 ≤ (8477485397/19531250000 : ℝ)^6411 := by
    have hnat : (5312421941 : ℕ)^8459*19531250000^6411 ≤ 8477485397^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312421941 10000000000 8477485397 19531250000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023705461/5000000000 : ℝ)^8459 ≤ (3083960569391/25000000000000 : ℝ)^6411 := by
    have hnat : (1023705461 : ℕ)^8459*25000000000000^6411 ≤ 3083960569391^6411*5000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023705461 5000000000 3083960569391 25000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391517403/10000000000 : ℝ)^8459 ≤ (44259432473593/100000000000000 : ℝ)^6411 := by
    have hnat : (5391517403 : ℕ)^8459*100000000000000^6411 ≤ 44259432473593^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391517403 10000000000 44259432473593 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312421941/10000000000 : ℝ), (-1023705461/5000000000 : ℝ), (5391517403/10000000000 : ℝ)] ![(8477485397/19531250000 : ℝ), (3083960569391/25000000000000 : ℝ), (44259432473593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312421941/10000000000 : ℝ)|^8459 ≤ (8477485397/19531250000 : ℝ)^6411
        have hw : |(5312421941/10000000000 : ℝ)|=(5312421941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023705461/5000000000 : ℝ)|^8459 ≤ (3083960569391/25000000000000 : ℝ)^6411
        have hw : |(-1023705461/5000000000 : ℝ)|=(1023705461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391517403/10000000000 : ℝ)|^8459 ≤ (44259432473593/100000000000000 : ℝ)^6411
        have hw : |(5391517403/10000000000 : ℝ)|=(5391517403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_6 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312421947/10000000000 : ℝ)*x 0 + (5391517401/10000000000 : ℝ)*x 1 + (-2047410917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312421947/10000000000 : ℝ)^8459 ≤ (43404725297323/100000000000000 : ℝ)^6411 := by
    have hnat : (5312421947 : ℕ)^8459*100000000000000^6411 ≤ 43404725297323^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312421947 10000000000 43404725297323 100000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391517401/10000000000 : ℝ)^8459 ≤ (4425943245193/10000000000000 : ℝ)^6411 := by
    have hnat : (5391517401 : ℕ)^8459*10000000000000^6411 ≤ 4425943245193^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391517401 10000000000 4425943245193 10000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2047410917/10000000000 : ℝ)^8459 ≤ (2467168447563/20000000000000 : ℝ)^6411 := by
    have hnat : (2047410917 : ℕ)^8459*20000000000000^6411 ≤ 2467168447563^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047410917 10000000000 2467168447563 20000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312421947/10000000000 : ℝ), (5391517401/10000000000 : ℝ), (-2047410917/10000000000 : ℝ)] ![(43404725297323/100000000000000 : ℝ), (4425943245193/10000000000000 : ℝ), (2467168447563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312421947/10000000000 : ℝ)|^8459 ≤ (43404725297323/100000000000000 : ℝ)^6411
        have hw : |(5312421947/10000000000 : ℝ)|=(5312421947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391517401/10000000000 : ℝ)|^8459 ≤ (4425943245193/10000000000000 : ℝ)^6411
        have hw : |(5391517401/10000000000 : ℝ)|=(5391517401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2047410917/10000000000 : ℝ)|^8459 ≤ (2467168447563/20000000000000 : ℝ)^6411
        have hw : |(-2047410917/10000000000 : ℝ)|=(2047410917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1266_s5_7 (p : ℝ) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347447953/10000000000 : ℝ)*x 0 + (559540001/1250000000 : ℝ)*x 1 + (4222186681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347447953/10000000000 : ℝ)^8459 ≤ (4164645497437/12500000000000 : ℝ)^6411 := by
    have hnat : (4347447953 : ℕ)^8459*12500000000000^6411 ≤ 4164645497437^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347447953 10000000000 4164645497437 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559540001/1250000000 : ℝ)^8459 ≤ (4328302083031/12500000000000 : ℝ)^6411 := by
    have hnat : (559540001 : ℕ)^8459*12500000000000^6411 ≤ 4328302083031^6411*1250000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559540001 1250000000 4328302083031 12500000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222186681/10000000000 : ℝ)^8459 ≤ (16028209666563/50000000000000 : ℝ)^6411 := by
    have hnat : (4222186681 : ℕ)^8459*50000000000000^6411 ≤ 16028209666563^6411*10000000000^8459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222186681 10000000000 16028209666563 50000000000000 8459 6411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8459/2048 : ℝ)) 8459 6411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347447953/10000000000 : ℝ), (559540001/1250000000 : ℝ), (4222186681/10000000000 : ℝ)] ![(4164645497437/12500000000000 : ℝ), (4328302083031/12500000000000 : ℝ), (16028209666563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347447953/10000000000 : ℝ)|^8459 ≤ (4164645497437/12500000000000 : ℝ)^6411
        have hw : |(4347447953/10000000000 : ℝ)|=(4347447953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559540001/1250000000 : ℝ)|^8459 ≤ (4328302083031/12500000000000 : ℝ)^6411
        have hw : |(559540001/1250000000 : ℝ)|=(559540001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222186681/10000000000 : ℝ)|^8459 ≤ (16028209666563/50000000000000 : ℝ)^6411
        have hw : |(4222186681/10000000000 : ℝ)|=(4222186681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1266_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2297/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (707/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/10000 : ℝ) ^ (4229/1024 : ℝ) ≤ (12692686226529509/100000000000000000000 : ℝ) := by
    have hpowers : (1139/10000 : ℝ)^4229 ≤ (12692686226529509/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1139 : ℕ)^4229*100000000000000000000^1024 ≤ 12692686226529509^1024*10000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 10000 12692686226529509 100000000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/10000 : ℝ)) (X := (12692686226529509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (4229/1024 : ℝ) ≤ (255305095299579/800000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^4229 ≤ (255305095299579/800000000000000000 : ℝ)^1024 := by
      have hnat : (14239 : ℕ)^4229*800000000000000000^1024 ≤ 255305095299579^1024*100000^4229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 255305095299579 800000000000000000 4229 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (255305095299579/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012692686226529509/50000000000000000000 : ℝ) ≤ (5000307308125571/5000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (50012692686226529509/50000000000000000000 : ℝ)^1024 ≤ (5000307308125571/5000000000000000 : ℝ)^4229 := by
      have hnat : (50012692686226529509 : ℕ)^1024*5000000000000000^4229 ≤ 5000307308125571^4229*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012692686226529509 50000000000000000000 5000307308125571 5000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000307308125571/5000000000000000 : ℝ)) (X := (50012692686226529509/50000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011151455784744221/25000000000000000000 : ℝ) ≤ (40004319569113/40000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (25011151455784744221/25000000000000000000 : ℝ)^1024 ≤ (40004319569113/40000000000000 : ℝ)^4229 := by
      have hnat : (25011151455784744221 : ℕ)^1024*40000000000000^4229 ≤ 40004319569113^4229*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011151455784744221 25000000000000000000 40004319569113 40000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40004319569113/40000000000000 : ℝ)) (X := (25011151455784744221/25000000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400255305095299579/400000000000000000 : ℝ) ≤ (5000772584152679/5000000000000000 : ℝ) ^ (4229/1024 : ℝ) := by
    have hpowers : (400255305095299579/400000000000000000 : ℝ)^1024 ≤ (5000772584152679/5000000000000000 : ℝ)^4229 := by
      have hnat : (400255305095299579 : ℕ)^1024*5000000000000000^4229 ≤ 5000772584152679^4229*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400255305095299579 400000000000000000 5000772584152679 5000000000000000 1024 4229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000772584152679/5000000000000000 : ℝ)) (X := (400255305095299579/400000000000000000 : ℝ)) (by norm_num) 4229 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12692686226529509/100000000000000000000 : ℝ) ≤ ((14240576026900991659/14245000000000000000 : ℝ)+2*(116319006777/71225000000000 : ℝ)*(1139/10000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (14240576026900991659/14245000000000000000 : ℝ)+2*(116319006777/71225000000000 : ℝ)*(1139/10000 : ℝ)=(5000307308125571/5000000000000000 : ℝ) by norm_num, show 1+2*(12692686226529509/100000000000000000000 : ℝ)=(50012692686226529509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(255305095299579/800000000000000000 : ℝ)+(12692686226529509/100000000000000000000 : ℝ) ≤ ((14240576026900991659/14245000000000000000 : ℝ)+(116319006777/71225000000000 : ℝ)*((14239/100000 : ℝ)+(1139/10000 : ℝ)))^(4229/1024 : ℝ) := by
    rw [show (14240576026900991659/14245000000000000000 : ℝ)+(116319006777/71225000000000 : ℝ)*((14239/100000 : ℝ)+(1139/10000 : ℝ))=(40004319569113/40000000000000 : ℝ) by norm_num, show 1+(255305095299579/800000000000000000 : ℝ)+(12692686226529509/100000000000000000000 : ℝ)=(25011151455784744221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(255305095299579/800000000000000000 : ℝ) ≤ ((14240576026900991659/14245000000000000000 : ℝ)+2*(116319006777/71225000000000 : ℝ)*(14239/100000 : ℝ))^(4229/1024 : ℝ) := by
    rw [show (14240576026900991659/14245000000000000000 : ℝ)+2*(116319006777/71225000000000 : ℝ)*(14239/100000 : ℝ)=(5000772584152679/5000000000000000 : ℝ) by norm_num, show 1+2*(255305095299579/800000000000000000 : ℝ)=(400255305095299579/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14240576026900991659/14245000000000000000 : ℝ)*(X 1 0+X 2 0)+(116319006777/71225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (14240576026900991659/14245000000000000000 : ℝ)) (alpha := (116319006777/71225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14240576026900991659/14245000000000000000 : ℝ)*(X 0 1+X 2 1)+(116319006777/71225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (14240576026900991659/14245000000000000000 : ℝ)) (alpha := (116319006777/71225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14240576026900991659/14245000000000000000 : ℝ)*(X 0 2+X 1 2)+(116319006777/71225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4229/1024 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (14240576026900991659/14245000000000000000 : ℝ)) (alpha := (116319006777/71225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65902183/312500000 : ℝ)*X 0 0+(2695920123/5000000000 : ℝ)*X 0 1+(5266496681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672227449/5000000000 : ℝ)*X 1 0+(-543107941/2500000000 : ℝ)*X 1 1+(1316624177/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068890951/2000000000 : ℝ)*X 2 0+(1316624177/2500000000 : ℝ)*X 2 1+(-1086215977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173719117/5000000000 : ℝ)*X 0 0+(4221528491/10000000000 : ℝ)*X 0 1+(4476975621/10000000000 : ℝ)*X 0 2+(2173719117/5000000000 : ℝ)*X 1 0+(4221528491/10000000000 : ℝ)*X 1 1+(4476975621/10000000000 : ℝ)*X 1 2+(2173719117/5000000000 : ℝ)*X 2 0+(4221528491/10000000000 : ℝ)*X 2 1+(4476975621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108874501/10000000000 : ℝ)*X 0 0+(5266818481/10000000000 : ℝ)*X 0 1+(5391517407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312421941/10000000000 : ℝ)*X 1 0+(-1023705461/5000000000 : ℝ)*X 1 1+(5391517403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312421947/10000000000 : ℝ)*X 2 0+(5391517401/10000000000 : ℝ)*X 2 1+(-2047410917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347447953/10000000000 : ℝ)*X 0 0+(559540001/1250000000 : ℝ)*X 0 1+(4222186681/10000000000 : ℝ)*X 0 2+(4347447953/10000000000 : ℝ)*X 1 0+(559540001/1250000000 : ℝ)*X 1 1+(4222186681/10000000000 : ℝ)*X 1 2+(4347447953/10000000000 : ℝ)*X 2 0+(559540001/1250000000 : ℝ)*X 2 1+(4222186681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1266_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1868159844961491069154477041/356125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224651149/25000000000000 : ℝ)*(base19) + (577994221/100000000000000 : ℝ)*(base23) + (429912227/100000000000000 : ℝ)*(upper3) + (28630997/50000000000000 : ℝ)*(upper4) + (140481/3125000000000 : ℝ)*(upper5) + (5946406980456433/100000000000000 : ℝ)*(major0) + (5946406980456433/100000000000000 : ℝ)*(major1) + (5946406980456433/100000000000000 : ℝ)*(major2) + (7978095293165707/100000000000000 : ℝ)*(sp0) + (797809575300919/10000000000000 : ℝ)*(sp1) + (1994524018404891/25000000000000 : ℝ)*(sp2) + (978676684128113/25000000000000 : ℝ)*(sp3) + (1358448079/100000000000000 : ℝ)*(sp4) + (5198963341/50000000000000 : ℝ)*(sp7) + (3914717134439133/100000000000000 : ℝ)*(f.failure) + (1595619330322757/20000000000000 : ℝ)*(f.sum) + (26683184847729/14245000000000000000000000000 : ℝ)*base65 + (1077536879839673423/129500000000000000000000000000000 : ℝ)*base68 + (1751036522967173423/129500000000000000000000000000000 : ℝ)*base70 + (1123246368577173423/129500000000000000000000000000000 : ℝ)*base72 + (63442924869/890312500000000000000000000 : ℝ)*base73 + (183570711517173423/129500000000000000000000000000000 : ℝ)*base76 + (1789694057477173423/129500000000000000000000000000000 : ℝ)*base78 + (2322536981025826577/129500000000000000000000000000000 : ℝ)*base79 + (43229555670173/7122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5925851/2000000000000000000000 : ℝ)*base90 + (5925851/2000000000000000000000 : ℝ)*base92 + (5925851/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (152013556156604914989306399/35612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375724693/50000000000000 : ℝ)*(base19) + (419468033/50000000000000 : ℝ)*(base23) + (10418027/12500000000000 : ℝ)*(upper3) + (8692757/25000000000000 : ℝ)*(lower4) + (541741/625000000000 : ℝ)*(upper5) + (597712838980713/10000000000000 : ℝ)*(major0) + (597712838980713/10000000000000 : ℝ)*(major1) + (597712838980713/10000000000000 : ℝ)*(major2) + (20776736177/100000000000000 : ℝ)*(sp1) + (229290013/1000000000000 : ℝ)*(sp2) + (8019314579171723/100000000000000 : ℝ)*(sp4) + (100241163137327/1250000000000 : ℝ)*(sp5) + (8019290811234357/100000000000000 : ℝ)*(sp6) + (1967471029078851/50000000000000 : ℝ)*(sp7) + (1967471029078851/50000000000000 : ℝ)*(f.failure) + (8019314579171723/100000000000000 : ℝ)*(f.sum) + (5144093546759/2849000000000000000000000000 : ℝ)*base66 + (60593668689683897/12950000000000000000000000000000 : ℝ)*base67 + (60617821164883897/12950000000000000000000000000000 : ℝ)*base69 + (35789871517333897/12950000000000000000000000000000 : ℝ)*base71 + (2354865362019/712250000000000000000000000 : ℝ)*base73 + (22927292486633897/12950000000000000000000000000000 : ℝ)*base75 + (13169326778016103/12950000000000000000000000000000 : ℝ)*base78 + (88264532057383897/12950000000000000000000000000000 : ℝ)*base79 + (10778959732451/2849000000000000000000000000 : ℝ)*base81 + (10903803/1000000000000000000000 : ℝ)*base89 + (10903803/1000000000000000000000 : ℝ)*base91 + (10903803/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1266_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (707/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1266_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1266_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (707/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1266_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1266_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1266_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4229/1024 : ℝ) ≤ p) (hpb : p ≤ (8459/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30379753/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16161/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2399/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (707/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1266_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
