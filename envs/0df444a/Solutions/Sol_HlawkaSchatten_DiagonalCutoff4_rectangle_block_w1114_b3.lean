-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:06:34.561822+00:00
-- url     : https://prove2.me/submissions/857aa4cc-8ce2-487f-bf8d-d7f1e412a27f

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
theorem support_rectangle_w1114_box_0 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-128282697/625000000 : ℝ)*x 0 + (2688353547/5000000000 : ℝ)*x 1 + (5376706383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128282697/625000000 : ℝ)^8307 ≤ (3056347019919/25000000000000 : ℝ)^6259 := by
    have hnat : (128282697 : ℕ)^8307*25000000000000^6259 ≤ 3056347019919^6259*625000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128282697 625000000 3056347019919 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688353547/5000000000 : ℝ)^8307 ≤ (43887309807959/100000000000000 : ℝ)^6259 := by
    have hnat : (2688353547 : ℕ)^8307*100000000000000^6259 ≤ 43887309807959^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688353547 5000000000 43887309807959 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376706383/10000000000 : ℝ)^8307 ≤ (5485912763183/12500000000000 : ℝ)^6259 := by
    have hnat : (5376706383 : ℕ)^8307*12500000000000^6259 ≤ 5485912763183^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376706383 10000000000 5485912763183 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128282697/625000000 : ℝ), (2688353547/5000000000 : ℝ), (5376706383/10000000000 : ℝ)] ![(3056347019919/25000000000000 : ℝ), (43887309807959/100000000000000 : ℝ), (5485912763183/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128282697/625000000 : ℝ)|^8307 ≤ (3056347019919/25000000000000 : ℝ)^6259
        have hw : |(-128282697/625000000 : ℝ)|=(128282697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688353547/5000000000 : ℝ)|^8307 ≤ (43887309807959/100000000000000 : ℝ)^6259
        have hw : |(2688353547/5000000000 : ℝ)|=(2688353547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376706383/10000000000 : ℝ)|^8307 ≤ (5485912763183/12500000000000 : ℝ)^6259
        have hw : |(5376706383/10000000000 : ℝ)|=(5376706383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_1 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647856799/5000000000 : ℝ)*x 0 + (-2162292597/10000000000 : ℝ)*x 1 + (672088349/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647856799/5000000000 : ℝ)^8307 ≤ (43012050578663/100000000000000 : ℝ)^6259 := by
    have hnat : (2647856799 : ℕ)^8307*100000000000000^6259 ≤ 43012050578663^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647856799 5000000000 43012050578663 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162292597/10000000000 : ℝ)^8307 ≤ (6550321433553/50000000000000 : ℝ)^6259 := by
    have hnat : (2162292597 : ℕ)^8307*50000000000000^6259 ≤ 6550321433553^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162292597 10000000000 6550321433553 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672088349/1250000000 : ℝ)^8307 ≤ (21943653268147/50000000000000 : ℝ)^6259 := by
    have hnat : (672088349 : ℕ)^8307*50000000000000^6259 ≤ 21943653268147^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672088349 1250000000 21943653268147 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647856799/5000000000 : ℝ), (-2162292597/10000000000 : ℝ), (672088349/1250000000 : ℝ)] ![(43012050578663/100000000000000 : ℝ), (6550321433553/50000000000000 : ℝ), (21943653268147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647856799/5000000000 : ℝ)|^8307 ≤ (43012050578663/100000000000000 : ℝ)^6259
        have hw : |(2647856799/5000000000 : ℝ)|=(2647856799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2162292597/10000000000 : ℝ)|^8307 ≤ (6550321433553/50000000000000 : ℝ)^6259
        have hw : |(-2162292597/10000000000 : ℝ)|=(2162292597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672088349/1250000000 : ℝ)|^8307 ≤ (21943653268147/50000000000000 : ℝ)^6259
        have hw : |(672088349/1250000000 : ℝ)|=(672088349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_2 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647856857/5000000000 : ℝ)*x 0 + (5376706667/10000000000 : ℝ)*x 1 + (-216229261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647856857/5000000000 : ℝ)^8307 ≤ (2688253239319/6250000000000 : ℝ)^6259 := by
    have hnat : (2647856857 : ℕ)^8307*6250000000000^6259 ≤ 2688253239319^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647856857 5000000000 2688253239319 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376706667/10000000000 : ℝ)^8307 ≤ (2742956573883/6250000000000 : ℝ)^6259 := by
    have hnat : (5376706667 : ℕ)^8307*6250000000000^6259 ≤ 2742956573883^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376706667 10000000000 2742956573883 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216229261/1000000000 : ℝ)^8307 ≤ (13100642971641/100000000000000 : ℝ)^6259 := by
    have hnat : (216229261 : ℕ)^8307*100000000000000^6259 ≤ 13100642971641^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216229261 1000000000 13100642971641 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647856857/5000000000 : ℝ), (5376706667/10000000000 : ℝ), (-216229261/1000000000 : ℝ)] ![(2688253239319/6250000000000 : ℝ), (2742956573883/6250000000000 : ℝ), (13100642971641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647856857/5000000000 : ℝ)|^8307 ≤ (2688253239319/6250000000000 : ℝ)^6259
        have hw : |(2647856857/5000000000 : ℝ)|=(2647856857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376706667/10000000000 : ℝ)|^8307 ≤ (2742956573883/6250000000000 : ℝ)^6259
        have hw : |(5376706667/10000000000 : ℝ)|=(5376706667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216229261/1000000000 : ℝ)|^8307 ≤ (13100642971641/100000000000000 : ℝ)^6259
        have hw : |(-216229261/1000000000 : ℝ)|=(216229261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_3 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (895297059/2000000000 : ℝ)*x 0 + (4316838623/10000000000 : ℝ)*x 1 + (2158418343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895297059/2000000000 : ℝ)^8307 ≤ (17206428237379/50000000000000 : ℝ)^6259 := by
    have hnat : (895297059 : ℕ)^8307*50000000000000^6259 ≤ 17206428237379^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895297059 2000000000 17206428237379 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316838623/10000000000 : ℝ)^8307 ≤ (32793581519637/100000000000000 : ℝ)^6259 := by
    have hnat : (4316838623 : ℕ)^8307*100000000000000^6259 ≤ 32793581519637^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316838623 10000000000 32793581519637 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158418343/5000000000 : ℝ)^8307 ≤ (32793561990103/100000000000000 : ℝ)^6259 := by
    have hnat : (2158418343 : ℕ)^8307*100000000000000^6259 ≤ 32793561990103^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158418343 5000000000 32793561990103 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895297059/2000000000 : ℝ), (4316838623/10000000000 : ℝ), (2158418343/5000000000 : ℝ)] ![(17206428237379/50000000000000 : ℝ), (32793581519637/100000000000000 : ℝ), (32793561990103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895297059/2000000000 : ℝ)|^8307 ≤ (17206428237379/50000000000000 : ℝ)^6259
        have hw : |(895297059/2000000000 : ℝ)|=(895297059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316838623/10000000000 : ℝ)|^8307 ≤ (32793581519637/100000000000000 : ℝ)^6259
        have hw : |(4316838623/10000000000 : ℝ)|=(4316838623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2158418343/5000000000 : ℝ)|^8307 ≤ (32793561990103/100000000000000 : ℝ)^6259
        have hw : |(2158418343/5000000000 : ℝ)|=(2158418343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_4 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1154782681/5000000000 : ℝ)*x 0 + (5280771931/10000000000 : ℝ)*x 1 + (528077183/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1154782681/5000000000 : ℝ)^8307 ≤ (14297883187079/100000000000000 : ℝ)^6259 := by
    have hnat : (1154782681 : ℕ)^8307*100000000000000^6259 ≤ 14297883187079^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154782681 5000000000 14297883187079 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280771931/10000000000 : ℝ)^8307 ≤ (2678191183657/6250000000000 : ℝ)^6259 := by
    have hnat : (5280771931 : ℕ)^8307*6250000000000^6259 ≤ 2678191183657^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280771931 10000000000 2678191183657 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528077183/1000000000 : ℝ)^8307 ≤ (42851057850773/100000000000000 : ℝ)^6259 := by
    have hnat : (528077183 : ℕ)^8307*100000000000000^6259 ≤ 42851057850773^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528077183 1000000000 42851057850773 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1154782681/5000000000 : ℝ), (5280771931/10000000000 : ℝ), (528077183/1000000000 : ℝ)] ![(14297883187079/100000000000000 : ℝ), (2678191183657/6250000000000 : ℝ), (42851057850773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1154782681/5000000000 : ℝ)|^8307 ≤ (14297883187079/100000000000000 : ℝ)^6259
        have hw : |(-1154782681/5000000000 : ℝ)|=(1154782681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280771931/10000000000 : ℝ)|^8307 ≤ (2678191183657/6250000000000 : ℝ)^6259
        have hw : |(5280771931/10000000000 : ℝ)|=(5280771931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528077183/1000000000 : ℝ)|^8307 ≤ (42851057850773/100000000000000 : ℝ)^6259
        have hw : |(528077183/1000000000 : ℝ)|=(528077183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_5 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363534723/10000000000 : ℝ)*x 0 + (-17187077/78125000 : ℝ)*x 1 + (5280771701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363534723/10000000000 : ℝ)^8307 ≤ (43744666437041/100000000000000 : ℝ)^6259 := by
    have hnat : (5363534723 : ℕ)^8307*100000000000000^6259 ≤ 43744666437041^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363534723 10000000000 43744666437041 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17187077/78125000 : ℝ)^8307 ≤ (670213854251/5000000000000 : ℝ)^6259 := by
    have hnat : (17187077 : ℕ)^8307*5000000000000^6259 ≤ 670213854251^6259*78125000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17187077 78125000 670213854251 5000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280771701/10000000000 : ℝ)^8307 ≤ (21425528230741/50000000000000 : ℝ)^6259 := by
    have hnat : (5280771701 : ℕ)^8307*50000000000000^6259 ≤ 21425528230741^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280771701 10000000000 21425528230741 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363534723/10000000000 : ℝ), (-17187077/78125000 : ℝ), (5280771701/10000000000 : ℝ)] ![(43744666437041/100000000000000 : ℝ), (670213854251/5000000000000 : ℝ), (21425528230741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363534723/10000000000 : ℝ)|^8307 ≤ (43744666437041/100000000000000 : ℝ)^6259
        have hw : |(5363534723/10000000000 : ℝ)|=(5363534723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17187077/78125000 : ℝ)|^8307 ≤ (670213854251/5000000000000 : ℝ)^6259
        have hw : |(-17187077/78125000 : ℝ)|=(17187077/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280771701/10000000000 : ℝ)|^8307 ≤ (21425528230741/50000000000000 : ℝ)^6259
        have hw : |(5280771701/10000000000 : ℝ)|=(5280771701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_6 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072706889/2000000000 : ℝ)*x 0 + (1056154421/2000000000 : ℝ)*x 1 + (-219994569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072706889/2000000000 : ℝ)^8307 ≤ (2734041464237/6250000000000 : ℝ)^6259 := by
    have hnat : (1072706889 : ℕ)^8307*6250000000000^6259 ≤ 2734041464237^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072706889 2000000000 2734041464237 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056154421/2000000000 : ℝ)^8307 ≤ (42851060812439/100000000000000 : ℝ)^6259 := by
    have hnat : (1056154421 : ℕ)^8307*100000000000000^6259 ≤ 42851060812439^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056154421 2000000000 42851060812439 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219994569/1000000000 : ℝ)^8307 ≤ (1340427574263/10000000000000 : ℝ)^6259 := by
    have hnat : (219994569 : ℕ)^8307*10000000000000^6259 ≤ 1340427574263^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219994569 1000000000 1340427574263 10000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072706889/2000000000 : ℝ), (1056154421/2000000000 : ℝ), (-219994569/1000000000 : ℝ)] ![(2734041464237/6250000000000 : ℝ), (42851060812439/100000000000000 : ℝ), (1340427574263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072706889/2000000000 : ℝ)|^8307 ≤ (2734041464237/6250000000000 : ℝ)^6259
        have hw : |(1072706889/2000000000 : ℝ)|=(1072706889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056154421/2000000000 : ℝ)|^8307 ≤ (42851060812439/100000000000000 : ℝ)^6259
        have hw : |(1056154421/2000000000 : ℝ)|=(1056154421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219994569/1000000000 : ℝ)|^8307 ≤ (1340427574263/10000000000000 : ℝ)^6259
        have hw : |(-219994569/1000000000 : ℝ)|=(219994569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_7 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1065108869/2500000000 : ℝ)*x 0 + (884968381/2000000000 : ℝ)*x 1 + (2212420549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065108869/2500000000 : ℝ)^8307 ≤ (2014132735261/6250000000000 : ℝ)^6259 := by
    have hnat : (1065108869 : ℕ)^8307*6250000000000^6259 ≤ 2014132735261^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065108869 2500000000 2014132735261 6250000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884968381/2000000000 : ℝ)^8307 ≤ (33886942211719/100000000000000 : ℝ)^6259 := by
    have hnat : (884968381 : ℕ)^8307*100000000000000^6259 ≤ 33886942211719^6259*2000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884968381 2000000000 33886942211719 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2212420549/5000000000 : ℝ)^8307 ≤ (33886934009197/100000000000000 : ℝ)^6259 := by
    have hnat : (2212420549 : ℕ)^8307*100000000000000^6259 ≤ 33886934009197^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212420549 5000000000 33886934009197 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065108869/2500000000 : ℝ), (884968381/2000000000 : ℝ), (2212420549/5000000000 : ℝ)] ![(2014132735261/6250000000000 : ℝ), (33886942211719/100000000000000 : ℝ), (33886934009197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065108869/2500000000 : ℝ)|^8307 ≤ (2014132735261/6250000000000 : ℝ)^6259
        have hw : |(1065108869/2500000000 : ℝ)|=(1065108869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884968381/2000000000 : ℝ)|^8307 ≤ (33886942211719/100000000000000 : ℝ)^6259
        have hw : |(884968381/2000000000 : ℝ)|=(884968381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2212420549/5000000000 : ℝ)|^8307 ≤ (33886934009197/100000000000000 : ℝ)^6259
        have hw : |(2212420549/5000000000 : ℝ)|=(2212420549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_8 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2255847069/10000000000 : ℝ)*x 0 + (5215580941/10000000000 : ℝ)*x 1 + (5386313057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2255847069/10000000000 : ℝ)^8307 ≤ (1732275178901/12500000000000 : ℝ)^6259 := by
    have hnat : (2255847069 : ℕ)^8307*12500000000000^6259 ≤ 1732275178901^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255847069 10000000000 1732275178901 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215580941/10000000000 : ℝ)^8307 ≤ (1317199806311/3125000000000 : ℝ)^6259 := by
    have hnat : (5215580941 : ℕ)^8307*3125000000000^6259 ≤ 1317199806311^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215580941 10000000000 1317199806311 3125000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386313057/10000000000 : ℝ)^8307 ≤ (43991404748843/100000000000000 : ℝ)^6259 := by
    have hnat : (5386313057 : ℕ)^8307*100000000000000^6259 ≤ 43991404748843^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386313057 10000000000 43991404748843 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2255847069/10000000000 : ℝ), (5215580941/10000000000 : ℝ), (5386313057/10000000000 : ℝ)] ![(1732275178901/12500000000000 : ℝ), (1317199806311/3125000000000 : ℝ), (43991404748843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2255847069/10000000000 : ℝ)|^8307 ≤ (1732275178901/12500000000000 : ℝ)^6259
        have hw : |(-2255847069/10000000000 : ℝ)|=(2255847069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215580941/10000000000 : ℝ)|^8307 ≤ (1317199806311/3125000000000 : ℝ)^6259
        have hw : |(5215580941/10000000000 : ℝ)|=(5215580941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386313057/10000000000 : ℝ)|^8307 ≤ (43991404748843/100000000000000 : ℝ)^6259
        have hw : |(5386313057/10000000000 : ℝ)|=(5386313057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_9 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661114897/1250000000 : ℝ)*x 0 + (-107922577/500000000 : ℝ)*x 1 + (2693156779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661114897/1250000000 : ℝ)^8307 ≤ (42938824422413/100000000000000 : ℝ)^6259 := by
    have hnat : (661114897 : ℕ)^8307*100000000000000^6259 ≤ 42938824422413^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661114897 1250000000 42938824422413 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107922577/500000000 : ℝ)^8307 ≤ (51053771037/390625000000 : ℝ)^6259 := by
    have hnat : (107922577 : ℕ)^8307*390625000000^6259 ≤ 51053771037^6259*500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107922577 500000000 51053771037 390625000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693156779/5000000000 : ℝ)^8307 ≤ (43991410179511/100000000000000 : ℝ)^6259 := by
    have hnat : (2693156779 : ℕ)^8307*100000000000000^6259 ≤ 43991410179511^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693156779 5000000000 43991410179511 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661114897/1250000000 : ℝ), (-107922577/500000000 : ℝ), (2693156779/5000000000 : ℝ)] ![(42938824422413/100000000000000 : ℝ), (51053771037/390625000000 : ℝ), (43991410179511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661114897/1250000000 : ℝ)|^8307 ≤ (42938824422413/100000000000000 : ℝ)^6259
        have hw : |(661114897/1250000000 : ℝ)|=(661114897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107922577/500000000 : ℝ)|^8307 ≤ (51053771037/390625000000 : ℝ)^6259
        have hw : |(-107922577/500000000 : ℝ)|=(107922577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693156779/5000000000 : ℝ)|^8307 ≤ (43991410179511/100000000000000 : ℝ)^6259
        have hw : |(2693156779/5000000000 : ℝ)|=(2693156779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_10 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288919/10000000 : ℝ)*x 0 + (673289097/1250000000 : ℝ)*x 1 + (-215845283/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288919/10000000 : ℝ)^8307 ≤ (42938822525991/100000000000000 : ℝ)^6259 := by
    have hnat : (5288919 : ℕ)^8307*100000000000000^6259 ≤ 42938822525991^6259*10000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288919 10000000 42938822525991 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673289097/1250000000 : ℝ)^8307 ≤ (439914017029/1000000000000 : ℝ)^6259 := by
    have hnat : (673289097 : ℕ)^8307*1000000000000^6259 ≤ 439914017029^6259*1250000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673289097 1250000000 439914017029 1000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215845283/1000000000 : ℝ)^8307 ≤ (2613955150501/20000000000000 : ℝ)^6259 := by
    have hnat : (215845283 : ℕ)^8307*20000000000000^6259 ≤ 2613955150501^6259*1000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215845283 1000000000 2613955150501 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288919/10000000 : ℝ), (673289097/1250000000 : ℝ), (-215845283/1000000000 : ℝ)] ![(42938822525991/100000000000000 : ℝ), (439914017029/1000000000000 : ℝ), (2613955150501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288919/10000000 : ℝ)|^8307 ≤ (42938822525991/100000000000000 : ℝ)^6259
        have hw : |(5288919/10000000 : ℝ)|=(5288919/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673289097/1250000000 : ℝ)|^8307 ≤ (439914017029/1000000000000 : ℝ)^6259
        have hw : |(673289097/1250000000 : ℝ)|=(673289097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215845283/1000000000 : ℝ)|^8307 ≤ (2613955150501/20000000000000 : ℝ)^6259
        have hw : |(-215845283/1000000000 : ℝ)|=(215845283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_11 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (28111539/62500000 : ℝ)*x 0 + (17224067/40000000 : ℝ)*x 1 + (4306016537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28111539/62500000 : ℝ)^8307 ≤ (8657742404533/25000000000000 : ℝ)^6259 := by
    have hnat : (28111539 : ℕ)^8307*25000000000000^6259 ≤ 8657742404533^6259*62500000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28111539 62500000 8657742404533 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17224067/40000000 : ℝ)^8307 ≤ (16342258125881/50000000000000 : ℝ)^6259 := by
    have hnat : (17224067 : ℕ)^8307*50000000000000^6259 ≤ 16342258125881^6259*40000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17224067 40000000 16342258125881 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306016537/10000000000 : ℝ)^8307 ≤ (16342257052991/50000000000000 : ℝ)^6259 := by
    have hnat : (4306016537 : ℕ)^8307*50000000000000^6259 ≤ 16342257052991^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306016537 10000000000 16342257052991 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28111539/62500000 : ℝ), (17224067/40000000 : ℝ), (4306016537/10000000000 : ℝ)] ![(8657742404533/25000000000000 : ℝ), (16342258125881/50000000000000 : ℝ), (16342257052991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28111539/62500000 : ℝ)|^8307 ≤ (8657742404533/25000000000000 : ℝ)^6259
        have hw : |(28111539/62500000 : ℝ)|=(28111539/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17224067/40000000 : ℝ)|^8307 ≤ (16342258125881/50000000000000 : ℝ)^6259
        have hw : |(17224067/40000000 : ℝ)|=(17224067/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4306016537/10000000000 : ℝ)|^8307 ≤ (16342257052991/50000000000000 : ℝ)^6259
        have hw : |(4306016537/10000000000 : ℝ)|=(4306016537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_12 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053289471/5000000000 : ℝ)*x 0 + (5440599049/10000000000 : ℝ)*x 1 + (5272746067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053289471/5000000000 : ℝ)^8307 ≤ (12654541342919/100000000000000 : ℝ)^6259 := by
    have hnat : (1053289471 : ℕ)^8307*100000000000000^6259 ≤ 12654541342919^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053289471 5000000000 12654541342919 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440599049/10000000000 : ℝ)^8307 ≤ (22290407157561/50000000000000 : ℝ)^6259 := by
    have hnat : (5440599049 : ℕ)^8307*50000000000000^6259 ≤ 22290407157561^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440599049 10000000000 22290407157561 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272746067/10000000000 : ℝ)^8307 ≤ (10691161082603/25000000000000 : ℝ)^6259 := by
    have hnat : (5272746067 : ℕ)^8307*25000000000000^6259 ≤ 10691161082603^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272746067 10000000000 10691161082603 25000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053289471/5000000000 : ℝ), (5440599049/10000000000 : ℝ), (5272746067/10000000000 : ℝ)] ![(12654541342919/100000000000000 : ℝ), (22290407157561/50000000000000 : ℝ), (10691161082603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053289471/5000000000 : ℝ)|^8307 ≤ (12654541342919/100000000000000 : ℝ)^6259
        have hw : |(-1053289471/5000000000 : ℝ)|=(1053289471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440599049/10000000000 : ℝ)|^8307 ≤ (22290407157561/50000000000000 : ℝ)^6259
        have hw : |(5440599049/10000000000 : ℝ)|=(5440599049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272746067/10000000000 : ℝ)|^8307 ≤ (10691161082603/25000000000000 : ℝ)^6259
        have hw : |(5272746067/10000000000 : ℝ)|=(5272746067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_13 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684602783/5000000000 : ℝ)*x 0 + (-2203038379/10000000000 : ℝ)*x 1 + (5272746317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684602783/5000000000 : ℝ)^8307 ≤ (21903030929933/50000000000000 : ℝ)^6259 := by
    have hnat : (2684602783 : ℕ)^8307*50000000000000^6259 ≤ 21903030929933^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684602783 5000000000 21903030929933 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203038379/10000000000 : ℝ)^8307 ≤ (13429291101929/100000000000000 : ℝ)^6259 := by
    have hnat : (2203038379 : ℕ)^8307*100000000000000^6259 ≤ 13429291101929^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203038379 10000000000 13429291101929 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272746317/10000000000 : ℝ)^8307 ≤ (5345580877687/12500000000000 : ℝ)^6259 := by
    have hnat : (5272746317 : ℕ)^8307*12500000000000^6259 ≤ 5345580877687^6259*10000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272746317 10000000000 5345580877687 12500000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684602783/5000000000 : ℝ), (-2203038379/10000000000 : ℝ), (5272746317/10000000000 : ℝ)] ![(21903030929933/50000000000000 : ℝ), (13429291101929/100000000000000 : ℝ), (5345580877687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684602783/5000000000 : ℝ)|^8307 ≤ (21903030929933/50000000000000 : ℝ)^6259
        have hw : |(2684602783/5000000000 : ℝ)|=(2684602783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2203038379/10000000000 : ℝ)|^8307 ≤ (13429291101929/100000000000000 : ℝ)^6259
        have hw : |(-2203038379/10000000000 : ℝ)|=(2203038379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272746317/10000000000 : ℝ)|^8307 ≤ (5345580877687/12500000000000 : ℝ)^6259
        have hw : |(5272746317/10000000000 : ℝ)|=(5272746317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_14 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684603081/5000000000 : ℝ)*x 0 + (2636372993/5000000000 : ℝ)*x 1 + (-1101519011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684603081/5000000000 : ℝ)^8307 ≤ (43806068313579/100000000000000 : ℝ)^6259 := by
    have hnat : (2684603081 : ℕ)^8307*100000000000000^6259 ≤ 43806068313579^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684603081 5000000000 43806068313579 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636372993/5000000000 : ℝ)^8307 ≤ (42764643458501/100000000000000 : ℝ)^6259 := by
    have hnat : (2636372993 : ℕ)^8307*100000000000000^6259 ≤ 42764643458501^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636372993 5000000000 42764643458501 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101519011/5000000000 : ℝ)^8307 ≤ (6714644106827/50000000000000 : ℝ)^6259 := by
    have hnat : (1101519011 : ℕ)^8307*50000000000000^6259 ≤ 6714644106827^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101519011 5000000000 6714644106827 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684603081/5000000000 : ℝ), (2636372993/5000000000 : ℝ), (-1101519011/5000000000 : ℝ)] ![(43806068313579/100000000000000 : ℝ), (42764643458501/100000000000000 : ℝ), (6714644106827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684603081/5000000000 : ℝ)|^8307 ≤ (43806068313579/100000000000000 : ℝ)^6259
        have hw : |(2684603081/5000000000 : ℝ)|=(2684603081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636372993/5000000000 : ℝ)|^8307 ≤ (42764643458501/100000000000000 : ℝ)^6259
        have hw : |(2636372993/5000000000 : ℝ)|=(2636372993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1101519011/5000000000 : ℝ)|^8307 ≤ (6714644106827/50000000000000 : ℝ)^6259
        have hw : |(-1101519011/5000000000 : ℝ)|=(1101519011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1114_box_15 (p : ℝ) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060532619/2500000000 : ℝ)*x 0 + (138558497/312500000 : ℝ)*x 1 + (2216935983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060532619/2500000000 : ℝ)^8307 ≤ (16021243973791/50000000000000 : ℝ)^6259 := by
    have hnat : (1060532619 : ℕ)^8307*50000000000000^6259 ≤ 16021243973791^6259*2500000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060532619 2500000000 16021243973791 50000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138558497/312500000 : ℝ)^8307 ≤ (33978755701433/100000000000000 : ℝ)^6259 := by
    have hnat : (138558497 : ℕ)^8307*100000000000000^6259 ≤ 33978755701433^6259*312500000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138558497 312500000 33978755701433 100000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216935983/5000000000 : ℝ)^8307 ≤ (6795751266407/20000000000000 : ℝ)^6259 := by
    have hnat : (2216935983 : ℕ)^8307*20000000000000^6259 ≤ 6795751266407^6259*5000000000^8307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216935983 5000000000 6795751266407 20000000000000 8307 6259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8307/2048 : ℝ)) 8307 6259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060532619/2500000000 : ℝ), (138558497/312500000 : ℝ), (2216935983/5000000000 : ℝ)] ![(16021243973791/50000000000000 : ℝ), (33978755701433/100000000000000 : ℝ), (6795751266407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060532619/2500000000 : ℝ)|^8307 ≤ (16021243973791/50000000000000 : ℝ)^6259
        have hw : |(1060532619/2500000000 : ℝ)|=(1060532619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138558497/312500000 : ℝ)|^8307 ≤ (33978755701433/100000000000000 : ℝ)^6259
        have hw : |(138558497/312500000 : ℝ)|=(138558497/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216935983/5000000000 : ℝ)|^8307 ≤ (6795751266407/20000000000000 : ℝ)^6259
        have hw : |(2216935983/5000000000 : ℝ)|=(2216935983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1114_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59277/100000 : ℝ) ∧ (39861/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41531/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (877/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (877/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (877/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11317/100000 : ℝ) ^ (4153/1024 : ℝ) ≤ (14529548011501411/100000000000000000000 : ℝ) := by
    have hpowers : (11317/100000 : ℝ)^4153 ≤ (14529548011501411/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11317 : ℕ)^4153*100000000000000000000^1024 ≤ 14529548011501411^1024*100000^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11317 100000 14529548011501411 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11317/100000 : ℝ)) (X := (14529548011501411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (877/6250 : ℝ) ^ (4153/1024 : ℝ) ≤ (34753897415859303/100000000000000000000 : ℝ) := by
    have hpowers : (877/6250 : ℝ)^4153 ≤ (34753897415859303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (877 : ℕ)^4153*100000000000000000000^1024 ≤ 34753897415859303^1024*6250^4153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        877 6250 34753897415859303 100000000000000000000 4153 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (877/6250 : ℝ)) (X := (34753897415859303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014529548011501411/50000000000000000000 : ℝ) ≤ (1250089553507797/1250000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50014529548011501411/50000000000000000000 : ℝ)^1024 ≤ (1250089553507797/1250000000000000 : ℝ)^4153 := by
      have hnat : (50014529548011501411 : ℕ)^1024*1250000000000000^4153 ≤ 1250089553507797^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014529548011501411 50000000000000000000 1250089553507797 1250000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250089553507797/1250000000000000 : ℝ)) (X := (50014529548011501411/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024641722713680357/50000000000000000000 : ℝ) ≤ (2000242990037711/2000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50024641722713680357/50000000000000000000 : ℝ)^1024 ≤ (2000242990037711/2000000000000000 : ℝ)^4153 := by
      have hnat : (50024641722713680357 : ℕ)^1024*2000000000000000^4153 ≤ 2000242990037711^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024641722713680357 50000000000000000000 2000242990037711 2000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000242990037711/2000000000000000 : ℝ)) (X := (50024641722713680357/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034753897415859303/50000000000000000000 : ℝ) ≤ (5000856736157367/5000000000000000 : ℝ) ^ (4153/1024 : ℝ) := by
    have hpowers : (50034753897415859303/50000000000000000000 : ℝ)^1024 ≤ (5000856736157367/5000000000000000 : ℝ)^4153 := by
      have hnat : (50034753897415859303 : ℕ)^1024*5000000000000000^4153 ≤ 5000856736157367^4153*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034753897415859303 50000000000000000000 5000856736157367 5000000000000000 1024 4153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000856736157367/5000000000000000 : ℝ)) (X := (50034753897415859303/50000000000000000000 : ℝ)) (by norm_num) 4153 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14529548011501411/100000000000000000000 : ℝ) ≤ ((13570330776192707677/13575000000000000000 : ℝ)+2*(498522126179/271500000000000 : ℝ)*(11317/100000 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (13570330776192707677/13575000000000000000 : ℝ)+2*(498522126179/271500000000000 : ℝ)*(11317/100000 : ℝ)=(1250089553507797/1250000000000000 : ℝ) by norm_num, show 1+2*(14529548011501411/100000000000000000000 : ℝ)=(50014529548011501411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34753897415859303/100000000000000000000 : ℝ)+(14529548011501411/100000000000000000000 : ℝ) ≤ ((13570330776192707677/13575000000000000000 : ℝ)+(498522126179/271500000000000 : ℝ)*((877/6250 : ℝ)+(11317/100000 : ℝ)))^(4153/1024 : ℝ) := by
    rw [show (13570330776192707677/13575000000000000000 : ℝ)+(498522126179/271500000000000 : ℝ)*((877/6250 : ℝ)+(11317/100000 : ℝ))=(2000242990037711/2000000000000000 : ℝ) by norm_num, show 1+(34753897415859303/100000000000000000000 : ℝ)+(14529548011501411/100000000000000000000 : ℝ)=(50024641722713680357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34753897415859303/100000000000000000000 : ℝ) ≤ ((13570330776192707677/13575000000000000000 : ℝ)+2*(498522126179/271500000000000 : ℝ)*(877/6250 : ℝ))^(4153/1024 : ℝ) := by
    rw [show (13570330776192707677/13575000000000000000 : ℝ)+2*(498522126179/271500000000000 : ℝ)*(877/6250 : ℝ)=(5000856736157367/5000000000000000 : ℝ) by norm_num, show 1+2*(34753897415859303/100000000000000000000 : ℝ)=(50034753897415859303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13570330776192707677/13575000000000000000 : ℝ)*(X 1 0+X 2 0)+(498522126179/271500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (13570330776192707677/13575000000000000000 : ℝ)) (alpha := (498522126179/271500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13570330776192707677/13575000000000000000 : ℝ)*(X 0 1+X 2 1)+(498522126179/271500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (13570330776192707677/13575000000000000000 : ℝ)) (alpha := (498522126179/271500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13570330776192707677/13575000000000000000 : ℝ)*(X 0 2+X 1 2)+(498522126179/271500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4153/1024 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (877/6250 : ℝ)) (c := (13570330776192707677/13575000000000000000 : ℝ)) (alpha := (498522126179/271500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128282697/625000000 : ℝ)*X 0 0+(2688353547/5000000000 : ℝ)*X 0 1+(5376706383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647856799/5000000000 : ℝ)*X 1 0+(-2162292597/10000000000 : ℝ)*X 1 1+(672088349/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647856857/5000000000 : ℝ)*X 2 0+(5376706667/10000000000 : ℝ)*X 2 1+(-216229261/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((895297059/2000000000 : ℝ)*X 0 0+(4316838623/10000000000 : ℝ)*X 0 1+(2158418343/5000000000 : ℝ)*X 0 2+(895297059/2000000000 : ℝ)*X 1 0+(4316838623/10000000000 : ℝ)*X 1 1+(2158418343/5000000000 : ℝ)*X 1 2+(895297059/2000000000 : ℝ)*X 2 0+(4316838623/10000000000 : ℝ)*X 2 1+(2158418343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1154782681/5000000000 : ℝ)*X 0 0+(5280771931/10000000000 : ℝ)*X 0 1+(528077183/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363534723/10000000000 : ℝ)*X 1 0+(-17187077/78125000 : ℝ)*X 1 1+(5280771701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072706889/2000000000 : ℝ)*X 2 0+(1056154421/2000000000 : ℝ)*X 2 1+(-219994569/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065108869/2500000000 : ℝ)*X 0 0+(884968381/2000000000 : ℝ)*X 0 1+(2212420549/5000000000 : ℝ)*X 0 2+(1065108869/2500000000 : ℝ)*X 1 0+(884968381/2000000000 : ℝ)*X 1 1+(2212420549/5000000000 : ℝ)*X 1 2+(1065108869/2500000000 : ℝ)*X 2 0+(884968381/2000000000 : ℝ)*X 2 1+(2212420549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2255847069/10000000000 : ℝ)*X 0 0+(5215580941/10000000000 : ℝ)*X 0 1+(5386313057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661114897/1250000000 : ℝ)*X 1 0+(-107922577/500000000 : ℝ)*X 1 1+(2693156779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288919/10000000 : ℝ)*X 2 0+(673289097/1250000000 : ℝ)*X 2 1+(-215845283/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((28111539/62500000 : ℝ)*X 0 0+(17224067/40000000 : ℝ)*X 0 1+(4306016537/10000000000 : ℝ)*X 0 2+(28111539/62500000 : ℝ)*X 1 0+(17224067/40000000 : ℝ)*X 1 1+(4306016537/10000000000 : ℝ)*X 1 2+(28111539/62500000 : ℝ)*X 2 0+(17224067/40000000 : ℝ)*X 2 1+(4306016537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1053289471/5000000000 : ℝ)*X 0 0+(5440599049/10000000000 : ℝ)*X 0 1+(5272746067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684602783/5000000000 : ℝ)*X 1 0+(-2203038379/10000000000 : ℝ)*X 1 1+(5272746317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684603081/5000000000 : ℝ)*X 2 0+(2636372993/5000000000 : ℝ)*X 2 1+(-1101519011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1060532619/2500000000 : ℝ)*X 0 0+(138558497/312500000 : ℝ)*X 0 1+(2216935983/5000000000 : ℝ)*X 0 2+(1060532619/2500000000 : ℝ)*X 1 0+(138558497/312500000 : ℝ)*X 1 1+(2216935983/5000000000 : ℝ)*X 1 2+(1060532619/2500000000 : ℝ)*X 2 0+(138558497/312500000 : ℝ)*X 2 1+(2216935983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1114_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-1759819205308842088232384632587/2828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112763479/100000000000000 : ℝ)*(lower0) + (49686299/25000000000000 : ℝ)*(lower2) + (65064581/50000000000000 : ℝ)*(lower4) + (2020947/1562500000000 : ℝ)*(lower5) + (12177997286913/312500000000 : ℝ)*(major0) + (12177997286913/312500000000 : ℝ)*(major1) + (12177997286913/312500000000 : ℝ)*(major2) + (15202071773/100000000000000 : ℝ)*(sp1) + (5197973954499729/100000000000000 : ℝ)*(sp4) + (2598983108748469/50000000000000 : ℝ)*(sp5) + (2598893721732491/50000000000000 : ℝ)*(sp6) + (1308339363937537/50000000000000 : ℝ)*(sp7) + (7465068981/100000000000000 : ℝ)*(sp8) + (12123506483/6250000000000 : ℝ)*(sp14) + (1308339363937537/50000000000000 : ℝ)*(f.failure) + (519798141956871/10000000000000 : ℝ)*(f.sum) + (9789634395709/905000000000000000000000000 : ℝ)*base66 + (5523257167984623/353515625000000000000000000000 : ℝ)*base67 + (41900263636548859/2828125000000000000000000000000 : ℝ)*base69 + (8306345124891617/1414062500000000000000000000000 : ℝ)*base71 + (5460612981929/905000000000000000000000000 : ℝ)*base74 + (4815677538890873/353515625000000000000000000000 : ℝ)*base75 + (1907971715671999/176757812500000000000000000000 : ℝ)*base77 + (18391910838047867/1414062500000000000000000000000 : ℝ)*base79 + (213605067863/113125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4771943/625000000000000000000 : ℝ)*base90 + (4771943/625000000000000000000 : ℝ)*base92 + (4771943/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59277/100000 : ℝ) ≤ (2682392921583419132995147833/4525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11279959/4000000000000 : ℝ)*(upper3) + (35353509/10000000000000 : ℝ)*(upper4) + (403021451/100000000000000 : ℝ)*(lower5) + (1980337307271533/50000000000000 : ℝ)*(major0) + (1980337307271533/50000000000000 : ℝ)*(major1) + (1980337307271533/50000000000000 : ℝ)*(major2) + (5242118072041573/100000000000000 : ℝ)*(sp0) + (524204770928473/10000000000000 : ℝ)*(sp1) + (163815398040719/3125000000000 : ℝ)*(sp2) + (531889275509951/20000000000000 : ℝ)*(sp3) + (35131264969/100000000000000 : ℝ)*(sp6) + (3795610267/25000000000000 : ℝ)*(sp7) + (2449131601/25000000000000 : ℝ)*(sp8) + (80159283247/100000000000000 : ℝ)*(sp9) + (1329730779995411/50000000000000 : ℝ)*(f.failure) + (5242127868567977/100000000000000 : ℝ)*(f.sum) + (58020241407239/13575000000000000000000000000 : ℝ)*base65 + (2069715400963241159/678750000000000000000000000000000 : ℝ)*base68 + (6935073559025741159/678750000000000000000000000000000 : ℝ)*base70 + (3497217542184258841/678750000000000000000000000000000 : ℝ)*base71 + (148990733793689/13575000000000000000000000000 : ℝ)*base73 + (103338936028008841/678750000000000000000000000000000 : ℝ)*base75 + (2476509284165508841/678750000000000000000000000000000 : ℝ)*base77 + (5500090109544491159/678750000000000000000000000000000 : ℝ)*base80 + (35433491806507/6787500000000000000000000000 : ℝ)*base81 + (11145029/625000000000000000000 : ℝ)*base90 + (11145029/625000000000000000000 : ℝ)*base92 + (11145029/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (39861/50000 : ℝ) ≤ (360753275907301007200360033/452500000000000000000000000 : ℝ) := by norm_num
    linear_combination (59023681/50000000000000 : ℝ)*(upper0) + (8871033/25000000000000 : ℝ)*(upper1) + (105874149/25000000000000 : ℝ)*(upper2) + (720368137/100000000000000 : ℝ)*(lower5) + (885740553061279/20000000000000 : ℝ)*(major0) + (885740553061279/20000000000000 : ℝ)*(major1) + (885740553061279/20000000000000 : ℝ)*(major2) + (235790159499/50000000000000 : ℝ)*(sp1) + (202000550119/100000000000000 : ℝ)*(sp3) + (5857092844518079/100000000000000 : ℝ)*(sp8) + (5856632192651693/100000000000000 : ℝ)*(sp9) + (1464275943242673/25000000000000 : ℝ)*(sp10) + (1486762465068737/50000000000000 : ℝ)*(sp11) + (2732113153/25000000000000 : ℝ)*(sp12) + (2973726930687593/100000000000000 : ℝ)*(f.failure) + (1464275943242673/25000000000000 : ℝ)*(f.sum) + (6244693052291/2715000000000000000000000000 : ℝ)*base65 + (318740773235788883/271500000000000000000000000000000 : ℝ)*base67 + (312421959613288883/271500000000000000000000000000000 : ℝ)*base69 + (303826013983711117/271500000000000000000000000000000 : ℝ)*base72 + (248088958981/678750000000000000000000000 : ℝ)*base74 + (757736993601211117/271500000000000000000000000000000 : ℝ)*base76 + (2225787607885711117/271500000000000000000000000000000 : ℝ)*base78 + (7176270759688288883/271500000000000000000000000000000 : ℝ)*base79 + (3365250091639/2715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3028127/1250000000000000000000 : ℝ)*base90 + (3028127/1250000000000000000000 : ℝ)*base92 + (3028127/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41531/50000 : ℝ) ≤ (-46980266724949753248638668517899/56562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21041537/50000000000000 : ℝ)*(lower1) + (277472653/100000000000000 : ℝ)*(lower2) + (115730869/50000000000000 : ℝ)*(upper5) + (2231755666862587/50000000000000 : ℝ)*(major0) + (2231755666862587/50000000000000 : ℝ)*(major1) + (2231755666862587/50000000000000 : ℝ)*(major2) + (31286707587/100000000000000 : ℝ)*(sp0) + (272137062961/100000000000000 : ℝ)*(sp5) + (81783176557/20000000000000 : ℝ)*(sp6) + (21878110813/12500000000000 : ℝ)*(sp7) + (74469724957399/1250000000000 : ℝ)*(sp12) + (2978668573118273/50000000000000 : ℝ)*(sp13) + (5957200367416721/100000000000000 : ℝ)*(sp14) + (2996924704295603/100000000000000 : ℝ)*(sp15) + (2997099729182107/100000000000000 : ℝ)*(f.failure) + (5957609283299507/100000000000000 : ℝ)*(f.sum) + (72931072528523/6787500000000000000000000000 : ℝ)*base65 + (8481818720185130399/678750000000000000000000000000000 : ℝ)*base67 + (1719419668281380399/678750000000000000000000000000000 : ℝ)*base69 + (1886860899456380399/678750000000000000000000000000000 : ℝ)*base71 + (69711594949249/3393750000000000000000000000 : ℝ)*base73 + (1250085301876119601/678750000000000000000000000000000 : ℝ)*base76 + (7283904676476380399/678750000000000000000000000000000 : ℝ)*base77 + (3594725003136380399/678750000000000000000000000000000 : ℝ)*base79 + (19234671737801/3393750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9190173/1250000000000000000000 : ℝ)*base90 + (9190173/1250000000000000000000 : ℝ)*base92 + (9190173/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1114_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59277/100000 : ℝ) else (39861/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41531/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1114_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1114_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59277/100000 : ℝ) else (39861/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41531/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1114_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4153/1024 : ℝ) ≤ p) (hpb : p ≤ (8307/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18615961/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (877/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59277/100000 : ℝ) else (39861/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41531/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1114_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
