-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:06.949295+00:00
-- url     : https://prove2.me/submissions/1d102a3d-9087-4ce5-90d0-03ed9d564ccb

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
theorem support_rectangle_w1543_s0_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1653443199/10000000000 : ℝ)*x 0 + (2944678103/5000000000 : ℝ)*x 1 + (1217088797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1653443199/10000000000 : ℝ)^4583 ≤ (2462880044083/25000000000000 : ℝ)^3559 := by
    have hnat : (1653443199 : ℕ)^4583*25000000000000^3559 ≤ 2462880044083^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653443199 10000000000 2462880044083 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2944678103/5000000000 : ℝ)^4583 ≤ (12643038286813/25000000000000 : ℝ)^3559 := by
    have hnat : (2944678103 : ℕ)^4583*25000000000000^3559 ≤ 12643038286813^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944678103 5000000000 12643038286813 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217088797/2500000000 : ℝ)^4583 ≤ (309190051971/781250000000 : ℝ)^3559 := by
    have hnat : (1217088797 : ℕ)^4583*781250000000^3559 ≤ 309190051971^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217088797 2500000000 309190051971 781250000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1653443199/10000000000 : ℝ), (2944678103/5000000000 : ℝ), (1217088797/2500000000 : ℝ)] ![(2462880044083/25000000000000 : ℝ), (12643038286813/25000000000000 : ℝ), (309190051971/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1653443199/10000000000 : ℝ)|^4583 ≤ (2462880044083/25000000000000 : ℝ)^3559
        have hw : |(-1653443199/10000000000 : ℝ)|=(1653443199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2944678103/5000000000 : ℝ)|^4583 ≤ (12643038286813/25000000000000 : ℝ)^3559
        have hw : |(2944678103/5000000000 : ℝ)|=(2944678103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1217088797/2500000000 : ℝ)|^4583 ≤ (309190051971/781250000000 : ℝ)^3559
        have hw : |(1217088797/2500000000 : ℝ)|=(1217088797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341954191/625000000 : ℝ)*x 0 + (-277936519/1250000000 : ℝ)*x 1 + (4868355257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341954191/625000000 : ℝ)^4583 ≤ (45997077115839/100000000000000 : ℝ)^3559 := by
    have hnat : (341954191 : ℕ)^4583*100000000000000^3559 ≤ 45997077115839^3559*625000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341954191 625000000 45997077115839 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277936519/1250000000 : ℝ)^4583 ≤ (1442659549083/10000000000000 : ℝ)^3559 := by
    have hnat : (277936519 : ℕ)^4583*10000000000000^3559 ≤ 1442659549083^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277936519 1250000000 1442659549083 10000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4868355257/10000000000 : ℝ)^4583 ≤ (39576327374599/100000000000000 : ℝ)^3559 := by
    have hnat : (4868355257 : ℕ)^4583*100000000000000^3559 ≤ 39576327374599^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868355257 10000000000 39576327374599 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341954191/625000000 : ℝ), (-277936519/1250000000 : ℝ), (4868355257/10000000000 : ℝ)] ![(45997077115839/100000000000000 : ℝ), (1442659549083/10000000000000 : ℝ), (39576327374599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341954191/625000000 : ℝ)|^4583 ≤ (45997077115839/100000000000000 : ℝ)^3559
        have hw : |(341954191/625000000 : ℝ)|=(341954191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277936519/1250000000 : ℝ)|^4583 ≤ (1442659549083/10000000000000 : ℝ)^3559
        have hw : |(-277936519/1250000000 : ℝ)|=(277936519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4868355257/10000000000 : ℝ)|^4583 ≤ (39576327374599/100000000000000 : ℝ)^3559
        have hw : |(4868355257/10000000000 : ℝ)|=(4868355257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (683908373/1250000000 : ℝ)*x 0 + (2434177611/5000000000 : ℝ)*x 1 + (-2223492289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683908373/1250000000 : ℝ)^4583 ≤ (22998538168187/50000000000000 : ℝ)^3559 := by
    have hnat : (683908373 : ℕ)^4583*50000000000000^3559 ≤ 22998538168187^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683908373 1250000000 22998538168187 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434177611/5000000000 : ℝ)^4583 ≤ (39576327008209/100000000000000 : ℝ)^3559 := by
    have hnat : (2434177611 : ℕ)^4583*100000000000000^3559 ≤ 39576327008209^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434177611 5000000000 39576327008209 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223492289/10000000000 : ℝ)^4583 ≤ (577063865419/4000000000000 : ℝ)^3559 := by
    have hnat : (2223492289 : ℕ)^4583*4000000000000^3559 ≤ 577063865419^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223492289 10000000000 577063865419 4000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(683908373/1250000000 : ℝ), (2434177611/5000000000 : ℝ), (-2223492289/10000000000 : ℝ)] ![(22998538168187/50000000000000 : ℝ), (39576327008209/100000000000000 : ℝ), (577063865419/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(683908373/1250000000 : ℝ)|^4583 ≤ (22998538168187/50000000000000 : ℝ)^3559
        have hw : |(683908373/1250000000 : ℝ)|=(683908373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2434177611/5000000000 : ℝ)|^4583 ≤ (39576327008209/100000000000000 : ℝ)^3559
        have hw : |(2434177611/5000000000 : ℝ)|=(2434177611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223492289/10000000000 : ℝ)|^4583 ≤ (577063865419/4000000000000 : ℝ)^3559
        have hw : |(-2223492289/10000000000 : ℝ)|=(2223492289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4136886247/10000000000 : ℝ)*x 0 + (96623051/312500000 : ℝ)*x 1 + (5457806933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4136886247/10000000000 : ℝ)^4583 ≤ (401136727821/1250000000000 : ℝ)^3559 := by
    have hnat : (4136886247 : ℕ)^4583*1250000000000^3559 ≤ 401136727821^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136886247 10000000000 401136727821 1250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96623051/312500000 : ℝ)^4583 ≤ (11028825524379/50000000000000 : ℝ)^3559 := by
    have hnat : (96623051 : ℕ)^4583*50000000000000^3559 ≤ 11028825524379^3559*312500000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96623051 312500000 11028825524379 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457806933/10000000000 : ℝ)^4583 ≤ (11462852678079/25000000000000 : ℝ)^3559 := by
    have hnat : (5457806933 : ℕ)^4583*25000000000000^3559 ≤ 11462852678079^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457806933 10000000000 11462852678079 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4136886247/10000000000 : ℝ), (96623051/312500000 : ℝ), (5457806933/10000000000 : ℝ)] ![(401136727821/1250000000000 : ℝ), (11028825524379/50000000000000 : ℝ), (11462852678079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4136886247/10000000000 : ℝ)|^4583 ≤ (401136727821/1250000000000 : ℝ)^3559
        have hw : |(4136886247/10000000000 : ℝ)|=(4136886247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96623051/312500000 : ℝ)|^4583 ≤ (11028825524379/50000000000000 : ℝ)^3559
        have hw : |(96623051/312500000 : ℝ)|=(96623051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457806933/10000000000 : ℝ)|^4583 ≤ (11462852678079/25000000000000 : ℝ)^3559
        have hw : |(5457806933/10000000000 : ℝ)|=(5457806933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1656708587/10000000000 : ℝ)*x 0 + (4894237011/10000000000 : ℝ)*x 1 + (2931275699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656708587/10000000000 : ℝ)^4583 ≤ (4938290459731/50000000000000 : ℝ)^3559 := by
    have hnat : (1656708587 : ℕ)^4583*50000000000000^3559 ≤ 4938290459731^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656708587 10000000000 4938290459731 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4894237011/10000000000 : ℝ)^4583 ≤ (9961867907779/25000000000000 : ℝ)^3559 := by
    have hnat : (4894237011 : ℕ)^4583*25000000000000^3559 ≤ 9961867907779^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4894237011 10000000000 9961867907779 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2931275699/5000000000 : ℝ)^4583 ≤ (25137973717703/50000000000000 : ℝ)^3559 := by
    have hnat : (2931275699 : ℕ)^4583*50000000000000^3559 ≤ 25137973717703^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2931275699 5000000000 25137973717703 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1656708587/10000000000 : ℝ), (4894237011/10000000000 : ℝ), (2931275699/5000000000 : ℝ)] ![(4938290459731/50000000000000 : ℝ), (9961867907779/25000000000000 : ℝ), (25137973717703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1656708587/10000000000 : ℝ)|^4583 ≤ (4938290459731/50000000000000 : ℝ)^3559
        have hw : |(-1656708587/10000000000 : ℝ)|=(1656708587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4894237011/10000000000 : ℝ)|^4583 ≤ (9961867907779/25000000000000 : ℝ)^3559
        have hw : |(4894237011/10000000000 : ℝ)|=(4894237011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2931275699/5000000000 : ℝ)|^4583 ≤ (25137973717703/50000000000000 : ℝ)^3559
        have hw : |(2931275699/5000000000 : ℝ)|=(2931275699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596103829/5000000000 : ℝ)*x 0 + (-1229296201/10000000000 : ℝ)*x 1 + (586255131/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596103829/5000000000 : ℝ)^4583 ≤ (2687403027099/6250000000000 : ℝ)^3559 := by
    have hnat : (2596103829 : ℕ)^4583*6250000000000^3559 ≤ 2687403027099^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596103829 5000000000 2687403027099 6250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1229296201/10000000000 : ℝ)^4583 ≤ (3362802543339/50000000000000 : ℝ)^3559 := by
    have hnat : (1229296201 : ℕ)^4583*50000000000000^3559 ≤ 3362802543339^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229296201 10000000000 3362802543339 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586255131/1000000000 : ℝ)^4583 ≤ (12568986615901/25000000000000 : ℝ)^3559 := by
    have hnat : (586255131 : ℕ)^4583*25000000000000^3559 ≤ 12568986615901^3559*1000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586255131 1000000000 12568986615901 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596103829/5000000000 : ℝ), (-1229296201/10000000000 : ℝ), (586255131/1000000000 : ℝ)] ![(2687403027099/6250000000000 : ℝ), (3362802543339/50000000000000 : ℝ), (12568986615901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596103829/5000000000 : ℝ)|^4583 ≤ (2687403027099/6250000000000 : ℝ)^3559
        have hw : |(2596103829/5000000000 : ℝ)|=(2596103829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1229296201/10000000000 : ℝ)|^4583 ≤ (3362802543339/50000000000000 : ℝ)^3559
        have hw : |(-1229296201/10000000000 : ℝ)|=(1229296201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(586255131/1000000000 : ℝ)|^4583 ≤ (12568986615901/25000000000000 : ℝ)^3559
        have hw : |(586255131/1000000000 : ℝ)|=(586255131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192206683/10000000000 : ℝ)*x 0 + (5862552719/10000000000 : ℝ)*x 1 + (-1229295467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192206683/10000000000 : ℝ)^4583 ≤ (343987504289/800000000000 : ℝ)^3559 := by
    have hnat : (5192206683 : ℕ)^4583*800000000000^3559 ≤ 343987504289^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192206683 10000000000 343987504289 800000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5862552719/10000000000 : ℝ)^4583 ≤ (12568990505873/25000000000000 : ℝ)^3559 := by
    have hnat : (5862552719 : ℕ)^4583*25000000000000^3559 ≤ 12568990505873^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5862552719 10000000000 12568990505873 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229295467/10000000000 : ℝ)^4583 ≤ (6725599915461/100000000000000 : ℝ)^3559 := by
    have hnat : (1229295467 : ℕ)^4583*100000000000000^3559 ≤ 6725599915461^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229295467 10000000000 6725599915461 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192206683/10000000000 : ℝ), (5862552719/10000000000 : ℝ), (-1229295467/10000000000 : ℝ)] ![(343987504289/800000000000 : ℝ), (12568990505873/25000000000000 : ℝ), (6725599915461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192206683/10000000000 : ℝ)|^4583 ≤ (343987504289/800000000000 : ℝ)^3559
        have hw : |(5192206683/10000000000 : ℝ)|=(5192206683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5862552719/10000000000 : ℝ)|^4583 ≤ (12568990505873/25000000000000 : ℝ)^3559
        have hw : |(5862552719/10000000000 : ℝ)|=(5862552719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1229295467/10000000000 : ℝ)|^4583 ≤ (6725599915461/100000000000000 : ℝ)^3559
        have hw : |(-1229295467/10000000000 : ℝ)|=(1229295467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s0_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4144450029/10000000000 : ℝ)*x 0 + (5397832187/10000000000 : ℝ)*x 1 + (3154047793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4144450029/10000000000 : ℝ)^4583 ≤ (16083257110581/50000000000000 : ℝ)^3559 := by
    have hnat : (4144450029 : ℕ)^4583*50000000000000^3559 ≤ 16083257110581^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144450029 10000000000 16083257110581 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397832187/10000000000 : ℝ)^4583 ≤ (45203618209571/100000000000000 : ℝ)^3559 := by
    have hnat : (5397832187 : ℕ)^4583*100000000000000^3559 ≤ 45203618209571^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397832187 10000000000 45203618209571 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154047793/10000000000 : ℝ)^4583 ≤ (5657466886719/25000000000000 : ℝ)^3559 := by
    have hnat : (3154047793 : ℕ)^4583*25000000000000^3559 ≤ 5657466886719^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154047793 10000000000 5657466886719 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4144450029/10000000000 : ℝ), (5397832187/10000000000 : ℝ), (3154047793/10000000000 : ℝ)] ![(16083257110581/50000000000000 : ℝ), (45203618209571/100000000000000 : ℝ), (5657466886719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4144450029/10000000000 : ℝ)|^4583 ≤ (16083257110581/50000000000000 : ℝ)^3559
        have hw : |(4144450029/10000000000 : ℝ)|=(4144450029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397832187/10000000000 : ℝ)|^4583 ≤ (45203618209571/100000000000000 : ℝ)^3559
        have hw : |(5397832187/10000000000 : ℝ)|=(5397832187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154047793/10000000000 : ℝ)|^4583 ≤ (5657466886719/25000000000000 : ℝ)^3559
        have hw : |(3154047793/10000000000 : ℝ)|=(3154047793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25089/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4581/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4581 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4581*1^1024 ≤ 0^1024*1^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4581/1024 : ℝ) ≤ (1658679662897480059/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4581 ≤ (1658679662897480059/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4581*100000000000000000000^1024 ≤ 1658679662897480059^1024*5^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1658679662897480059 100000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1658679662897480059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4581 := by
      have hnat : (1 : ℕ)^1024*1^4581 ≤ 1^4581*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101658679662897480059/100000000000000000000 : ℝ) ≤ (5018420177563927/5000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (101658679662897480059/100000000000000000000 : ℝ)^1024 ≤ (5018420177563927/5000000000000000 : ℝ)^4581 := by
      have hnat : (101658679662897480059 : ℕ)^1024*5000000000000000^4581 ≤ 5018420177563927^4581*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101658679662897480059 100000000000000000000 5018420177563927 5000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018420177563927/5000000000000000 : ℝ)) (X := (101658679662897480059/100000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51658679662897480059/50000000000000000000 : ℝ) ≤ (2518420177563927/2500000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (51658679662897480059/50000000000000000000 : ℝ)^1024 ≤ (2518420177563927/2500000000000000 : ℝ)^4581 := by
      have hnat : (51658679662897480059 : ℕ)^1024*2500000000000000^4581 ≤ 2518420177563927^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51658679662897480059 50000000000000000000 2518420177563927 2500000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2518420177563927/2500000000000000 : ℝ)) (X := (51658679662897480059/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(18420177563927/2000000000000000 : ℝ)*(0 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18420177563927/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1658679662897480059/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(18420177563927/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (1 : ℝ)+(18420177563927/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5018420177563927/5000000000000000 : ℝ) by norm_num, show 1+(1658679662897480059/100000000000000000000 : ℝ)+(0 : ℝ)=(101658679662897480059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1658679662897480059/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(18420177563927/2000000000000000 : ℝ)*(2/5 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18420177563927/2000000000000000 : ℝ)*(2/5 : ℝ)=(2518420177563927/2500000000000000 : ℝ) by norm_num, show 1+2*(1658679662897480059/100000000000000000000 : ℝ)=(51658679662897480059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(18420177563927/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18420177563927/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(18420177563927/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18420177563927/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(18420177563927/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18420177563927/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1653443199/10000000000 : ℝ)*X 0 0+(2944678103/5000000000 : ℝ)*X 0 1+(1217088797/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((341954191/625000000 : ℝ)*X 1 0+(-277936519/1250000000 : ℝ)*X 1 1+(4868355257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((683908373/1250000000 : ℝ)*X 2 0+(2434177611/5000000000 : ℝ)*X 2 1+(-2223492289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4136886247/10000000000 : ℝ)*X 0 0+(96623051/312500000 : ℝ)*X 0 1+(5457806933/10000000000 : ℝ)*X 0 2+(4136886247/10000000000 : ℝ)*X 1 0+(96623051/312500000 : ℝ)*X 1 1+(5457806933/10000000000 : ℝ)*X 1 2+(4136886247/10000000000 : ℝ)*X 2 0+(96623051/312500000 : ℝ)*X 2 1+(5457806933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1656708587/10000000000 : ℝ)*X 0 0+(4894237011/10000000000 : ℝ)*X 0 1+(2931275699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596103829/5000000000 : ℝ)*X 1 0+(-1229296201/10000000000 : ℝ)*X 1 1+(586255131/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192206683/10000000000 : ℝ)*X 2 0+(5862552719/10000000000 : ℝ)*X 2 1+(-1229295467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4144450029/10000000000 : ℝ)*X 0 0+(5397832187/10000000000 : ℝ)*X 0 1+(3154047793/10000000000 : ℝ)*X 0 2+(4144450029/10000000000 : ℝ)*X 1 0+(5397832187/10000000000 : ℝ)*X 1 1+(3154047793/10000000000 : ℝ)*X 1 2+(4144450029/10000000000 : ℝ)*X 2 0+(5397832187/10000000000 : ℝ)*X 2 1+(3154047793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (272108266176397591651797/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13781237/20000000000000 : ℝ)*(base1) + (1096313039/100000000000000 : ℝ)*(base19) + (541711989/50000000000000 : ℝ)*(base23) + (40362401/25000000000000 : ℝ)*(upper3) + (58786131/50000000000000 : ℝ)*(upper5) + (43816239092623/6250000000000 : ℝ)*(major0) + (43816239092623/6250000000000 : ℝ)*(major1) + (701059825481969/100000000000000 : ℝ)*(major2) + (489717427691597/50000000000000 : ℝ)*(sp0) + (979437455531857/100000000000000 : ℝ)*(sp1) + (489718734210459/50000000000000 : ℝ)*(sp2) + (422679130620637/100000000000000 : ℝ)*(sp3) + (3765367887/100000000000000 : ℝ)*(sp4) + (859093349/50000000000000 : ℝ)*(sp7) + (422680917713519/100000000000000 : ℝ)*(f.failure) + (979438551844897/100000000000000 : ℝ)*(f.sum) + (505044072099401/200000000000000000000000000000 : ℝ)*base66 + (1551312482867737/200000000000000000000000000000 : ℝ)*base68 + (68387052448021/12500000000000000000000000000 : ℝ)*base69 + (1315666231267737/200000000000000000000000000000 : ℝ)*base72 + (885488780099401/200000000000000000000000000000 : ℝ)*base74 + (98351355560521/12500000000000000000000000000 : ℝ)*base75 + (47202504551979/12500000000000000000000000000 : ℝ)*base78 + (67621617214479/12500000000000000000000000000 : ℝ)*base80 + (3564396720729/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22255143/10000000000000000000000 : ℝ)*base89 + (22255143/10000000000000000000000 : ℝ)*base91 + (77744857/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (507130032715280193942561/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (639423493/50000000000000 : ℝ)*(base19) + (1548874567/100000000000000 : ℝ)*(base23) + (123180069/25000000000000 : ℝ)*(base39) + (74381691/50000000000000 : ℝ)*(upper3) + (108588847/25000000000000 : ℝ)*(upper5) + (23099918546083/3125000000000 : ℝ)*(major0) + (23099918546083/3125000000000 : ℝ)*(major1) + (739196900754381/100000000000000 : ℝ)*(major2) + (933581119/25000000000000 : ℝ)*(sp1) + (26263141/781250000000 : ℝ)*(sp2) + (258179854427259/25000000000000 : ℝ)*(sp4) + (516357202268787/50000000000000 : ℝ)*(sp5) + (1032714999872697/100000000000000 : ℝ)*(sp6) + (111418676869163/25000000000000 : ℝ)*(sp7) + (111418676869163/25000000000000 : ℝ)*(f.failure) + (8068124300229/781250000000 : ℝ)*(f.sum) + (18664908051701/200000000000000000000000000000 : ℝ)*base66 + (1085188711185813/200000000000000000000000000000 : ℝ)*base68 + (50540994422941/6250000000000000000000000000 : ℝ)*base69 + (117591701614187/200000000000000000000000000000 : ℝ)*base71 + (486584592451701/200000000000000000000000000000 : ℝ)*base74 + (28558119772941/6250000000000000000000000000 : ℝ)*base75 + (15334623245809/6250000000000000000000000000 : ℝ)*base78 + (33544032820809/6250000000000000000000000000 : ℝ)*base80 + (284259483727/390625000000000000000000000 : ℝ)*base81 + (5321411/2500000000000000000000 : ℝ)*base89 + (5321411/2500000000000000000000 : ℝ)*base91 + (19678589/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1543_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1543_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1543_s1_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-112435487/625000000 : ℝ)*x 0 + (86730373/156250000 : ℝ)*x 1 + (204531987/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112435487/625000000 : ℝ)^4583 ≤ (10981907239163/100000000000000 : ℝ)^3559 := by
    have hnat : (112435487 : ℕ)^4583*100000000000000^3559 ≤ 10981907239163^3559*625000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112435487 625000000 10981907239163 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86730373/156250000 : ℝ)^4583 ≤ (4685927741089/10000000000000 : ℝ)^3559 := by
    have hnat : (86730373 : ℕ)^4583*10000000000000^3559 ≤ 4685927741089^3559*156250000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86730373 156250000 4685927741089 10000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204531987/400000000 : ℝ)^4583 ≤ (42158815341551/100000000000000 : ℝ)^3559 := by
    have hnat : (204531987 : ℕ)^4583*100000000000000^3559 ≤ 42158815341551^3559*400000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204531987 400000000 42158815341551 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112435487/625000000 : ℝ), (86730373/156250000 : ℝ), (204531987/400000000 : ℝ)] ![(10981907239163/100000000000000 : ℝ), (4685927741089/10000000000000 : ℝ), (42158815341551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112435487/625000000 : ℝ)|^4583 ≤ (10981907239163/100000000000000 : ℝ)^3559
        have hw : |(-112435487/625000000 : ℝ)|=(112435487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86730373/156250000 : ℝ)|^4583 ≤ (4685927741089/10000000000000 : ℝ)^3559
        have hw : |(86730373/156250000 : ℝ)|=(86730373/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204531987/400000000 : ℝ)|^4583 ≤ (42158815341551/100000000000000 : ℝ)^3559
        have hw : |(204531987/400000000 : ℝ)|=(204531987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107621681/200000000 : ℝ)*x 0 + (-2028459841/10000000000 : ℝ)*x 1 + (639162481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107621681/200000000 : ℝ)^4583 ≤ (4502308872017/10000000000000 : ℝ)^3559 := by
    have hnat : (107621681 : ℕ)^4583*10000000000000^3559 ≤ 4502308872017^3559*200000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107621681 200000000 4502308872017 10000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2028459841/10000000000 : ℝ)^4583 ≤ (12818094079463/100000000000000 : ℝ)^3559 := by
    have hnat : (2028459841 : ℕ)^4583*100000000000000^3559 ≤ 12818094079463^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028459841 10000000000 12818094079463 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639162481/1250000000 : ℝ)^4583 ≤ (21079408589161/50000000000000 : ℝ)^3559 := by
    have hnat : (639162481 : ℕ)^4583*50000000000000^3559 ≤ 21079408589161^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639162481 1250000000 21079408589161 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107621681/200000000 : ℝ), (-2028459841/10000000000 : ℝ), (639162481/1250000000 : ℝ)] ![(4502308872017/10000000000000 : ℝ), (12818094079463/100000000000000 : ℝ), (21079408589161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107621681/200000000 : ℝ)|^4583 ≤ (4502308872017/10000000000000 : ℝ)^3559
        have hw : |(107621681/200000000 : ℝ)|=(107621681/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2028459841/10000000000 : ℝ)|^4583 ≤ (12818094079463/100000000000000 : ℝ)^3559
        have hw : |(-2028459841/10000000000 : ℝ)|=(2028459841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639162481/1250000000 : ℝ)|^4583 ≤ (21079408589161/50000000000000 : ℝ)^3559
        have hw : |(639162481/1250000000 : ℝ)|=(639162481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690542169/5000000000 : ℝ)*x 0 + (255664983/500000000 : ℝ)*x 1 + (-1014229853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690542169/5000000000 : ℝ)^4583 ≤ (11255772955789/25000000000000 : ℝ)^3559 := by
    have hnat : (2690542169 : ℕ)^4583*25000000000000^3559 ≤ 11255772955789^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690542169 5000000000 11255772955789 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255664983/500000000 : ℝ)^4583 ≤ (42158815182293/100000000000000 : ℝ)^3559 := by
    have hnat : (255664983 : ℕ)^4583*100000000000000^3559 ≤ 42158815182293^3559*500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255664983 500000000 42158815182293 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014229853/5000000000 : ℝ)^4583 ≤ (12818092980931/100000000000000 : ℝ)^3559 := by
    have hnat : (1014229853 : ℕ)^4583*100000000000000^3559 ≤ 12818092980931^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014229853 5000000000 12818092980931 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690542169/5000000000 : ℝ), (255664983/500000000 : ℝ), (-1014229853/5000000000 : ℝ)] ![(11255772955789/25000000000000 : ℝ), (42158815182293/100000000000000 : ℝ), (12818092980931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690542169/5000000000 : ℝ)|^4583 ≤ (11255772955789/25000000000000 : ℝ)^3559
        have hw : |(2690542169/5000000000 : ℝ)|=(2690542169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(255664983/500000000 : ℝ)|^4583 ≤ (42158815182293/100000000000000 : ℝ)^3559
        have hw : |(255664983/500000000 : ℝ)|=(255664983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1014229853/5000000000 : ℝ)|^4583 ≤ (12818092980931/100000000000000 : ℝ)^3559
        have hw : |(-1014229853/5000000000 : ℝ)|=(1014229853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059574829/2500000000 : ℝ)*x 0 + (1878215607/5000000000 : ℝ)*x 1 + (596259949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059574829/2500000000 : ℝ)^4583 ≤ (16553762843963/50000000000000 : ℝ)^3559 := by
    have hnat : (1059574829 : ℕ)^4583*50000000000000^3559 ≤ 16553762843963^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059574829 2500000000 16553762843963 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878215607/5000000000 : ℝ)^4583 ≤ (28341921472511/100000000000000 : ℝ)^3559 := by
    have hnat : (1878215607 : ℕ)^4583*100000000000000^3559 ≤ 28341921472511^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878215607 5000000000 28341921472511 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596259949/1250000000 : ℝ)^4583 ≤ (2409409551493/6250000000000 : ℝ)^3559 := by
    have hnat : (596259949 : ℕ)^4583*6250000000000^3559 ≤ 2409409551493^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596259949 1250000000 2409409551493 6250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059574829/2500000000 : ℝ), (1878215607/5000000000 : ℝ), (596259949/1250000000 : ℝ)] ![(16553762843963/50000000000000 : ℝ), (28341921472511/100000000000000 : ℝ), (2409409551493/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059574829/2500000000 : ℝ)|^4583 ≤ (16553762843963/50000000000000 : ℝ)^3559
        have hw : |(1059574829/2500000000 : ℝ)|=(1059574829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1878215607/5000000000 : ℝ)|^4583 ≤ (28341921472511/100000000000000 : ℝ)^3559
        have hw : |(1878215607/5000000000 : ℝ)|=(1878215607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(596259949/1250000000 : ℝ)|^4583 ≤ (2409409551493/6250000000000 : ℝ)^3559
        have hw : |(596259949/1250000000 : ℝ)|=(596259949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-899608469/5000000000 : ℝ)*x 0 + (5117983457/10000000000 : ℝ)*x 1 + (277299403/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899608469/5000000000 : ℝ)^4583 ≤ (10983865807927/100000000000000 : ℝ)^3559 := by
    have hnat : (899608469 : ℕ)^4583*100000000000000^3559 ≤ 10983865807927^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899608469 5000000000 10983865807927 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5117983457/10000000000 : ℝ)^4583 ≤ (105521376079/250000000000 : ℝ)^3559 := by
    have hnat : (5117983457 : ℕ)^4583*250000000000^3559 ≤ 105521376079^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117983457 10000000000 105521376079 250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277299403/500000000 : ℝ)^4583 ≤ (2340379186829/5000000000000 : ℝ)^3559 := by
    have hnat : (277299403 : ℕ)^4583*5000000000000^3559 ≤ 2340379186829^3559*500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277299403 500000000 2340379186829 5000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899608469/5000000000 : ℝ), (5117983457/10000000000 : ℝ), (277299403/500000000 : ℝ)] ![(10983865807927/100000000000000 : ℝ), (105521376079/250000000000 : ℝ), (2340379186829/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899608469/5000000000 : ℝ)|^4583 ≤ (10983865807927/100000000000000 : ℝ)^3559
        have hw : |(-899608469/5000000000 : ℝ)|=(899608469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5117983457/10000000000 : ℝ)|^4583 ≤ (105521376079/250000000000 : ℝ)^3559
        have hw : |(5117983457/10000000000 : ℝ)|=(5117983457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277299403/500000000 : ℝ)|^4583 ≤ (2340379186829/5000000000000 : ℝ)^3559
        have hw : |(277299403/500000000 : ℝ)|=(277299403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263272721/500000000 : ℝ)*x 0 + (-797886219/5000000000 : ℝ)*x 1 + (5545987943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263272721/500000000 : ℝ)^4583 ≤ (43781136277157/100000000000000 : ℝ)^3559 := by
    have hnat : (263272721 : ℕ)^4583*100000000000000^3559 ≤ 43781136277157^3559*500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263272721 500000000 43781136277157 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (797886219/5000000000 : ℝ)^4583 ≤ (4705640622677/50000000000000 : ℝ)^3559 := by
    have hnat : (797886219 : ℕ)^4583*50000000000000^3559 ≤ 4705640622677^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797886219 5000000000 4705640622677 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5545987943/10000000000 : ℝ)^4583 ≤ (11701895616249/25000000000000 : ℝ)^3559 := by
    have hnat : (5545987943 : ℕ)^4583*25000000000000^3559 ≤ 11701895616249^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5545987943 10000000000 11701895616249 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263272721/500000000 : ℝ), (-797886219/5000000000 : ℝ), (5545987943/10000000000 : ℝ)] ![(43781136277157/100000000000000 : ℝ), (4705640622677/50000000000000 : ℝ), (11701895616249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263272721/500000000 : ℝ)|^4583 ≤ (43781136277157/100000000000000 : ℝ)^3559
        have hw : |(263272721/500000000 : ℝ)|=(263272721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-797886219/5000000000 : ℝ)|^4583 ≤ (4705640622677/50000000000000 : ℝ)^3559
        have hw : |(-797886219/5000000000 : ℝ)|=(797886219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5545987943/10000000000 : ℝ)|^4583 ≤ (11701895616249/25000000000000 : ℝ)^3559
        have hw : |(5545987943/10000000000 : ℝ)|=(5545987943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329090953/625000000 : ℝ)*x 0 + (2772993891/5000000000 : ℝ)*x 1 + (-3191543/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329090953/625000000 : ℝ)^4583 ≤ (2189057257133/5000000000000 : ℝ)^3559 := by
    have hnat : (329090953 : ℕ)^4583*5000000000000^3559 ≤ 2189057257133^3559*625000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329090953 625000000 2189057257133 5000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2772993891/5000000000 : ℝ)^4583 ≤ (46807580715209/100000000000000 : ℝ)^3559 := by
    have hnat : (2772993891 : ℕ)^4583*100000000000000^3559 ≤ 46807580715209^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772993891 5000000000 46807580715209 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191543/20000000 : ℝ)^4583 ≤ (4705637060853/50000000000000 : ℝ)^3559 := by
    have hnat : (3191543 : ℕ)^4583*50000000000000^3559 ≤ 4705637060853^3559*20000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191543 20000000 4705637060853 50000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329090953/625000000 : ℝ), (2772993891/5000000000 : ℝ), (-3191543/20000000 : ℝ)] ![(2189057257133/5000000000000 : ℝ), (46807580715209/100000000000000 : ℝ), (4705637060853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329090953/625000000 : ℝ)|^4583 ≤ (2189057257133/5000000000000 : ℝ)^3559
        have hw : |(329090953/625000000 : ℝ)|=(329090953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2772993891/5000000000 : ℝ)|^4583 ≤ (46807580715209/100000000000000 : ℝ)^3559
        have hw : |(2772993891/5000000000 : ℝ)|=(2772993891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3191543/20000000 : ℝ)|^4583 ≤ (4705637060853/50000000000000 : ℝ)^3559
        have hw : |(-3191543/20000000 : ℝ)|=(3191543/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s1_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238876453/10000000000 : ℝ)*x 0 + (2379612727/5000000000 : ℝ)*x 1 + (3679152/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238876453/10000000000 : ℝ)^4583 ≤ (33113331251629/100000000000000 : ℝ)^3559 := by
    have hnat : (4238876453 : ℕ)^4583*100000000000000^3559 ≤ 33113331251629^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238876453 10000000000 33113331251629 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2379612727/5000000000 : ℝ)^4583 ≤ (4804703808617/12500000000000 : ℝ)^3559 := by
    have hnat : (2379612727 : ℕ)^4583*12500000000000^3559 ≤ 4804703808617^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379612727 5000000000 4804703808617 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679152/9765625 : ℝ)^4583 ≤ (7112259565369/25000000000000 : ℝ)^3559 := by
    have hnat : (3679152 : ℕ)^4583*25000000000000^3559 ≤ 7112259565369^3559*9765625^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679152 9765625 7112259565369 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238876453/10000000000 : ℝ), (2379612727/5000000000 : ℝ), (3679152/9765625 : ℝ)] ![(33113331251629/100000000000000 : ℝ), (4804703808617/12500000000000 : ℝ), (7112259565369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238876453/10000000000 : ℝ)|^4583 ≤ (33113331251629/100000000000000 : ℝ)^3559
        have hw : |(4238876453/10000000000 : ℝ)|=(4238876453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2379612727/5000000000 : ℝ)|^4583 ≤ (4804703808617/12500000000000 : ℝ)^3559
        have hw : |(2379612727/5000000000 : ℝ)|=(2379612727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679152/9765625 : ℝ)|^4583 ≤ (7112259565369/25000000000000 : ℝ)^3559
        have hw : |(3679152/9765625 : ℝ)|=(3679152/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8753/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4503/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1609/50000 : ℝ) ^ (4581/1024 : ℝ) ≤ (21061434009187/100000000000000000000 : ℝ) := by
    have hpowers : (1609/50000 : ℝ)^4581 ≤ (21061434009187/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1609 : ℕ)^4581*100000000000000000000^1024 ≤ 21061434009187^1024*50000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1609 50000 21061434009187 100000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1609/50000 : ℝ)) (X := (21061434009187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25089/100000 : ℝ) ^ (4581/1024 : ℝ) ≤ (205830162463143739/100000000000000000000 : ℝ) := by
    have hpowers : (25089/100000 : ℝ)^4581 ≤ (205830162463143739/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25089 : ℕ)^4581*100000000000000000000^1024 ≤ 205830162463143739^1024*100000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25089 100000 205830162463143739 100000000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25089/100000 : ℝ)) (X := (205830162463143739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000021061434009187/50000000000000000000 : ℝ) ≤ (2000000188316131/2000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (50000021061434009187/50000000000000000000 : ℝ)^1024 ≤ (2000000188316131/2000000000000000 : ℝ)^4581 := by
      have hnat : (50000021061434009187 : ℕ)^1024*2000000000000000^4581 ≤ 2000000188316131^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000021061434009187 50000000000000000000 2000000188316131 2000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000188316131/2000000000000000 : ℝ)) (X := (50000021061434009187/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50102925611948576463/50000000000000000000 : ℝ) ≤ (5002298880123463/5000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (50102925611948576463/50000000000000000000 : ℝ)^1024 ≤ (5002298880123463/5000000000000000 : ℝ)^4581 := by
      have hnat : (50102925611948576463 : ℕ)^1024*5000000000000000^4581 ≤ 5002298880123463^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50102925611948576463 50000000000000000000 5002298880123463 5000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002298880123463/5000000000000000 : ℝ)) (X := (50102925611948576463/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50205830162463143739/50000000000000000000 : ℝ) ≤ (10009194578913197/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (50205830162463143739/50000000000000000000 : ℝ)^1024 ≤ (10009194578913197/10000000000000000 : ℝ)^4581 := by
      have hnat : (50205830162463143739 : ℕ)^1024*10000000000000000^4581 ≤ 10009194578913197^4581*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50205830162463143739 50000000000000000000 10009194578913197 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009194578913197/10000000000000000 : ℝ)) (X := (50205830162463143739/50000000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(21061434009187/100000000000000000000 : ℝ) ≤ ((218680435468374385349/218710000000000000000 : ℝ)+2*(4596818666271/2187100000000000 : ℝ)*(1609/50000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (218680435468374385349/218710000000000000000 : ℝ)+2*(4596818666271/2187100000000000 : ℝ)*(1609/50000 : ℝ)=(2000000188316131/2000000000000000 : ℝ) by norm_num, show 1+2*(21061434009187/100000000000000000000 : ℝ)=(50000021061434009187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(205830162463143739/100000000000000000000 : ℝ)+(21061434009187/100000000000000000000 : ℝ) ≤ ((218680435468374385349/218710000000000000000 : ℝ)+(4596818666271/2187100000000000 : ℝ)*((25089/100000 : ℝ)+(1609/50000 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (218680435468374385349/218710000000000000000 : ℝ)+(4596818666271/2187100000000000 : ℝ)*((25089/100000 : ℝ)+(1609/50000 : ℝ))=(5002298880123463/5000000000000000 : ℝ) by norm_num, show 1+(205830162463143739/100000000000000000000 : ℝ)+(21061434009187/100000000000000000000 : ℝ)=(50102925611948576463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(205830162463143739/100000000000000000000 : ℝ) ≤ ((218680435468374385349/218710000000000000000 : ℝ)+2*(4596818666271/2187100000000000 : ℝ)*(25089/100000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (218680435468374385349/218710000000000000000 : ℝ)+2*(4596818666271/2187100000000000 : ℝ)*(25089/100000 : ℝ)=(10009194578913197/10000000000000000 : ℝ) by norm_num, show 1+2*(205830162463143739/100000000000000000000 : ℝ)=(50205830162463143739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (218680435468374385349/218710000000000000000 : ℝ)*(X 1 0+X 2 0)+(4596818666271/2187100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (1609/50000 : ℝ)) (hi := (25089/100000 : ℝ)) (c := (218680435468374385349/218710000000000000000 : ℝ)) (alpha := (4596818666271/2187100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (218680435468374385349/218710000000000000000 : ℝ)*(X 0 1+X 2 1)+(4596818666271/2187100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (1609/50000 : ℝ)) (hi := (25089/100000 : ℝ)) (c := (218680435468374385349/218710000000000000000 : ℝ)) (alpha := (4596818666271/2187100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (218680435468374385349/218710000000000000000 : ℝ)*(X 0 2+X 1 2)+(4596818666271/2187100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (1609/50000 : ℝ)) (hi := (25089/100000 : ℝ)) (c := (218680435468374385349/218710000000000000000 : ℝ)) (alpha := (4596818666271/2187100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-112435487/625000000 : ℝ)*X 0 0+(86730373/156250000 : ℝ)*X 0 1+(204531987/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107621681/200000000 : ℝ)*X 1 0+(-2028459841/10000000000 : ℝ)*X 1 1+(639162481/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2690542169/5000000000 : ℝ)*X 2 0+(255664983/500000000 : ℝ)*X 2 1+(-1014229853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1059574829/2500000000 : ℝ)*X 0 0+(1878215607/5000000000 : ℝ)*X 0 1+(596259949/1250000000 : ℝ)*X 0 2+(1059574829/2500000000 : ℝ)*X 1 0+(1878215607/5000000000 : ℝ)*X 1 1+(596259949/1250000000 : ℝ)*X 1 2+(1059574829/2500000000 : ℝ)*X 2 0+(1878215607/5000000000 : ℝ)*X 2 1+(596259949/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-899608469/5000000000 : ℝ)*X 0 0+(5117983457/10000000000 : ℝ)*X 0 1+(277299403/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263272721/500000000 : ℝ)*X 1 0+(-797886219/5000000000 : ℝ)*X 1 1+(5545987943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329090953/625000000 : ℝ)*X 2 0+(2772993891/5000000000 : ℝ)*X 2 1+(-3191543/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4238876453/10000000000 : ℝ)*X 0 0+(2379612727/5000000000 : ℝ)*X 0 1+(3679152/9765625 : ℝ)*X 0 2+(4238876453/10000000000 : ℝ)*X 1 0+(2379612727/5000000000 : ℝ)*X 1 1+(3679152/9765625 : ℝ)*X 1 2+(4238876453/10000000000 : ℝ)*X 2 0+(2379612727/5000000000 : ℝ)*X 2 1+(3679152/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36633618394543321242561425289/5467750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21357101/50000000000000 : ℝ)*(base1) + (109540883/10000000000000 : ℝ)*(base19) + (152219831/12500000000000 : ℝ)*(base23) + (108151499/100000000000000 : ℝ)*(upper3) + (12807557/6250000000000 : ℝ)*(upper5) + (818142025306313/50000000000000 : ℝ)*(major0) + (818142025306313/50000000000000 : ℝ)*(major1) + (818142025306313/50000000000000 : ℝ)*(major2) + (1143007048230887/50000000000000 : ℝ)*(sp0) + (1143011619694691/50000000000000 : ℝ)*(sp1) + (2286023117039563/100000000000000 : ℝ)*(sp2) + (493269803446311/50000000000000 : ℝ)*(sp3) + (5140525319/50000000000000 : ℝ)*(sp4) + (3893488741/100000000000000 : ℝ)*(sp7) + (246635885773891/25000000000000 : ℝ)*(f.failure) + (571506083699553/25000000000000 : ℝ)*(f.sum) + (13539569846231/109355000000000000000000000000 : ℝ)*base65 + (136428465961238708237/10935500000000000000000000000000000 : ℝ)*base67 + (116454664697075708237/10935500000000000000000000000000000 : ℝ)*base69 + (9904471376830791763/10935500000000000000000000000000000 : ℝ)*base72 + (385967242582673/54677500000000000000000000000 : ℝ)*base73 + (40425014489637291763/10935500000000000000000000000000000 : ℝ)*base76 + (10150063403182208237/10935500000000000000000000000000000 : ℝ)*base77 + (104514258078785708237/10935500000000000000000000000000000 : ℝ)*base79 + (71528679725897/13669375000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (13894373/2500000000000000000000 : ℝ)*base90 + (13894373/2500000000000000000000 : ℝ)*base92 + (13894373/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113663477175393656252357980323/10935500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382918173/25000000000000 : ℝ)*(base19) + (517289041/25000000000000 : ℝ)*(base23) + (32011401/12500000000000 : ℝ)*(upper3) + (14474871/50000000000000 : ℝ)*(lower4) + (325782417/100000000000000 : ℝ)*(upper5) + (1672360270189903/100000000000000 : ℝ)*(major0) + (1672360270189903/100000000000000 : ℝ)*(major1) + (1672360270189903/100000000000000 : ℝ)*(major2) + (1152046589/12500000000000 : ℝ)*(sp1) + (3614411213/25000000000000 : ℝ)*(sp2) + (29205321039353/1250000000000 : ℝ)*(sp4) + (584103733775709/25000000000000 : ℝ)*(sp5) + (292051144543403/12500000000000 : ℝ)*(sp6) + (252073627691307/25000000000000 : ℝ)*(sp7) + (252073627691307/25000000000000 : ℝ)*(f.failure) + (29205321039353/1250000000000 : ℝ)*(f.sum) + (363827407957507/109355000000000000000000000000 : ℝ)*base66 + (260136168636929768853/21871000000000000000000000000000000 : ℝ)*base68 + (59378562388121768853/21871000000000000000000000000000000 : ℝ)*base70 + (172354194021181768853/21871000000000000000000000000000000 : ℝ)*base72 + (838814501602247/109355000000000000000000000000 : ℝ)*base74 + (82387723191725768853/21871000000000000000000000000000000 : ℝ)*base76 + (177064787672949768853/21871000000000000000000000000000000 : ℝ)*base78 + (89264646479697768853/21871000000000000000000000000000000 : ℝ)*base80 + (23446865161353/109355000000000000000000000000 : ℝ)*base81 + (28338179/2500000000000000000000 : ℝ)*base89 + (28338179/2500000000000000000000 : ℝ)*base91 + (28338179/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1543_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8753/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4503/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1543_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1543_s2_0 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-910070191/5000000000 : ℝ)*x 0 + (681078921/1250000000 : ℝ)*x 1 + (5201653263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910070191/5000000000 : ℝ)^4583 ≤ (11148625395121/100000000000000 : ℝ)^3559 := by
    have hnat : (910070191 : ℕ)^4583*100000000000000^3559 ≤ 11148625395121^3559*5000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910070191 5000000000 11148625395121 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681078921/1250000000 : ℝ)^4583 ≤ (11438042828213/25000000000000 : ℝ)^3559 := by
    have hnat : (681078921 : ℕ)^4583*25000000000000^3559 ≤ 11438042828213^3559*1250000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681078921 1250000000 11438042828213 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5201653263/10000000000 : ℝ)^4583 ≤ (5387400410883/12500000000000 : ℝ)^3559 := by
    have hnat : (5201653263 : ℕ)^4583*12500000000000^3559 ≤ 5387400410883^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201653263 10000000000 5387400410883 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-910070191/5000000000 : ℝ), (681078921/1250000000 : ℝ), (5201653263/10000000000 : ℝ)] ![(11148625395121/100000000000000 : ℝ), (11438042828213/25000000000000 : ℝ), (5387400410883/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-910070191/5000000000 : ℝ)|^4583 ≤ (11148625395121/100000000000000 : ℝ)^3559
        have hw : |(-910070191/5000000000 : ℝ)|=(910070191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681078921/1250000000 : ℝ)|^4583 ≤ (11438042828213/25000000000000 : ℝ)^3559
        have hw : |(681078921/1250000000 : ℝ)|=(681078921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5201653263/10000000000 : ℝ)|^4583 ≤ (5387400410883/12500000000000 : ℝ)^3559
        have hw : |(5201653263/10000000000 : ℝ)|=(5201653263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_1 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354900473/10000000000 : ℝ)*x 0 + (-1947064651/10000000000 : ℝ)*x 1 + (5201653193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354900473/10000000000 : ℝ)^4583 ≤ (44741177806873/100000000000000 : ℝ)^3559 := by
    have hnat : (5354900473 : ℕ)^4583*100000000000000^3559 ≤ 44741177806873^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354900473 10000000000 44741177806873 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1947064651/10000000000 : ℝ)^4583 ≤ (1519952455883/12500000000000 : ℝ)^3559 := by
    have hnat : (1947064651 : ℕ)^4583*12500000000000^3559 ≤ 1519952455883^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947064651 10000000000 1519952455883 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5201653193/10000000000 : ℝ)^4583 ≤ (43099202540189/100000000000000 : ℝ)^3559 := by
    have hnat : (5201653193 : ℕ)^4583*100000000000000^3559 ≤ 43099202540189^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201653193 10000000000 43099202540189 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354900473/10000000000 : ℝ), (-1947064651/10000000000 : ℝ), (5201653193/10000000000 : ℝ)] ![(44741177806873/100000000000000 : ℝ), (1519952455883/12500000000000 : ℝ), (43099202540189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354900473/10000000000 : ℝ)|^4583 ≤ (44741177806873/100000000000000 : ℝ)^3559
        have hw : |(5354900473/10000000000 : ℝ)|=(5354900473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1947064651/10000000000 : ℝ)|^4583 ≤ (1519952455883/12500000000000 : ℝ)^3559
        have hw : |(-1947064651/10000000000 : ℝ)|=(1947064651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5201653193/10000000000 : ℝ)|^4583 ≤ (43099202540189/100000000000000 : ℝ)^3559
        have hw : |(5201653193/10000000000 : ℝ)|=(5201653193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_2 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338724981/2500000000 : ℝ)*x 0 + (5201653371/10000000000 : ℝ)*x 1 + (-486766287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338724981/2500000000 : ℝ)^4583 ≤ (44741171900101/100000000000000 : ℝ)^3559 := by
    have hnat : (1338724981 : ℕ)^4583*100000000000000^3559 ≤ 44741171900101^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338724981 2500000000 44741171900101 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5201653371/10000000000 : ℝ)^4583 ≤ (8619840887877/20000000000000 : ℝ)^3559 := by
    have hnat : (5201653371 : ℕ)^4583*20000000000000^3559 ≤ 8619840887877^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201653371 10000000000 8619840887877 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486766287/2500000000 : ℝ)^4583 ≤ (2431924728783/20000000000000 : ℝ)^3559 := by
    have hnat : (486766287 : ℕ)^4583*20000000000000^3559 ≤ 2431924728783^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486766287 2500000000 2431924728783 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338724981/2500000000 : ℝ), (5201653371/10000000000 : ℝ), (-486766287/2500000000 : ℝ)] ![(44741171900101/100000000000000 : ℝ), (8619840887877/20000000000000 : ℝ), (2431924728783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338724981/2500000000 : ℝ)|^4583 ≤ (44741171900101/100000000000000 : ℝ)^3559
        have hw : |(1338724981/2500000000 : ℝ)|=(1338724981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5201653371/10000000000 : ℝ)|^4583 ≤ (8619840887877/20000000000000 : ℝ)^3559
        have hw : |(5201653371/10000000000 : ℝ)|=(5201653371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-486766287/2500000000 : ℝ)|^4583 ≤ (2431924728783/20000000000000 : ℝ)^3559
        have hw : |(-486766287/2500000000 : ℝ)|=(486766287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_3 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265848691/625000000 : ℝ)*x 0 + (795078211/2000000000 : ℝ)*x 1 + (454768841/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265848691/625000000 : ℝ)^4583 ≤ (33261305004349/100000000000000 : ℝ)^3559 := by
    have hnat : (265848691 : ℕ)^4583*100000000000000^3559 ≤ 33261305004349^3559*625000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265848691 625000000 33261305004349 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795078211/2000000000 : ℝ)^4583 ≤ (30486875667/100000000000 : ℝ)^3559 := by
    have hnat : (795078211 : ℕ)^4583*100000000000^3559 ≤ 30486875667^3559*2000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795078211 2000000000 30486875667 100000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454768841/1000000000 : ℝ)^4583 ≤ (4531477414019/12500000000000 : ℝ)^3559 := by
    have hnat : (454768841 : ℕ)^4583*12500000000000^3559 ≤ 4531477414019^3559*1000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454768841 1000000000 4531477414019 12500000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265848691/625000000 : ℝ), (795078211/2000000000 : ℝ), (454768841/1000000000 : ℝ)] ![(33261305004349/100000000000000 : ℝ), (30486875667/100000000000 : ℝ), (4531477414019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265848691/625000000 : ℝ)|^4583 ≤ (33261305004349/100000000000000 : ℝ)^3559
        have hw : |(265848691/625000000 : ℝ)|=(265848691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795078211/2000000000 : ℝ)|^4583 ≤ (30486875667/100000000000 : ℝ)^3559
        have hw : |(795078211/2000000000 : ℝ)|=(795078211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454768841/1000000000 : ℝ)|^4583 ≤ (4531477414019/12500000000000 : ℝ)^3559
        have hw : |(454768841/1000000000 : ℝ)|=(454768841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_4 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182018567/1000000000 : ℝ)*x 0 + (5203154657/10000000000 : ℝ)*x 1 + (5447116721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182018567/1000000000 : ℝ)^4583 ≤ (696811412789/6250000000000 : ℝ)^3559 := by
    have hnat : (182018567 : ℕ)^4583*6250000000000^3559 ≤ 696811412789^3559*1000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182018567 1000000000 696811412789 6250000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203154657/10000000000 : ℝ)^4583 ≤ (43115223283677/100000000000000 : ℝ)^3559 := by
    have hnat : (5203154657 : ℕ)^4583*100000000000000^3559 ≤ 43115223283677^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203154657 10000000000 43115223283677 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447116721/10000000000 : ℝ)^4583 ≤ (45735794091757/100000000000000 : ℝ)^3559 := by
    have hnat : (5447116721 : ℕ)^4583*100000000000000^3559 ≤ 45735794091757^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447116721 10000000000 45735794091757 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182018567/1000000000 : ℝ), (5203154657/10000000000 : ℝ), (5447116721/10000000000 : ℝ)] ![(696811412789/6250000000000 : ℝ), (43115223283677/100000000000000 : ℝ), (45735794091757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182018567/1000000000 : ℝ)|^4583 ≤ (696811412789/6250000000000 : ℝ)^3559
        have hw : |(-182018567/1000000000 : ℝ)|=(182018567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203154657/10000000000 : ℝ)|^4583 ≤ (43115223283677/100000000000000 : ℝ)^3559
        have hw : |(5203154657/10000000000 : ℝ)|=(5203154657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447116721/10000000000 : ℝ)|^4583 ≤ (45735794091757/100000000000000 : ℝ)^3559
        have hw : |(5447116721/10000000000 : ℝ)|=(5447116721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_5 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289769627/10000000000 : ℝ)*x 0 + (-106350089/625000000 : ℝ)*x 1 + (5447116711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289769627/10000000000 : ℝ)^4583 ≤ (44041655104891/100000000000000 : ℝ)^3559 := by
    have hnat : (5289769627 : ℕ)^4583*100000000000000^3559 ≤ 44041655104891^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289769627 10000000000 44041655104891 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106350089/625000000 : ℝ)^4583 ≤ (2044510178441/20000000000000 : ℝ)^3559 := by
    have hnat : (106350089 : ℕ)^4583*20000000000000^3559 ≤ 2044510178441^3559*625000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106350089 625000000 2044510178441 20000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447116711/10000000000 : ℝ)^4583 ≤ (11433948495909/25000000000000 : ℝ)^3559 := by
    have hnat : (5447116711 : ℕ)^4583*25000000000000^3559 ≤ 11433948495909^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447116711 10000000000 11433948495909 25000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289769627/10000000000 : ℝ), (-106350089/625000000 : ℝ), (5447116711/10000000000 : ℝ)] ![(44041655104891/100000000000000 : ℝ), (2044510178441/20000000000000 : ℝ), (11433948495909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289769627/10000000000 : ℝ)|^4583 ≤ (44041655104891/100000000000000 : ℝ)^3559
        have hw : |(5289769627/10000000000 : ℝ)|=(5289769627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106350089/625000000 : ℝ)|^4583 ≤ (2044510178441/20000000000000 : ℝ)^3559
        have hw : |(-106350089/625000000 : ℝ)|=(106350089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447116711/10000000000 : ℝ)|^4583 ≤ (11433948495909/25000000000000 : ℝ)^3559
        have hw : |(5447116711/10000000000 : ℝ)|=(5447116711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_6 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289769609/10000000000 : ℝ)*x 0 + (1361779211/2500000000 : ℝ)*x 1 + (-106350079/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289769609/10000000000 : ℝ)^4583 ≤ (44041654911907/100000000000000 : ℝ)^3559 := by
    have hnat : (5289769609 : ℕ)^4583*100000000000000^3559 ≤ 44041654911907^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289769609 10000000000 44041654911907 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361779211/2500000000 : ℝ)^4583 ≤ (914715908433/2000000000000 : ℝ)^3559 := by
    have hnat : (1361779211 : ℕ)^4583*2000000000000^3559 ≤ 914715908433^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361779211 2500000000 914715908433 2000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106350079/625000000 : ℝ)^4583 ≤ (408901986177/4000000000000 : ℝ)^3559 := by
    have hnat : (106350079 : ℕ)^4583*4000000000000^3559 ≤ 408901986177^3559*625000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106350079 625000000 408901986177 4000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289769609/10000000000 : ℝ), (1361779211/2500000000 : ℝ), (-106350079/625000000 : ℝ)] ![(44041654911907/100000000000000 : ℝ), (914715908433/2000000000000 : ℝ), (408901986177/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289769609/10000000000 : ℝ)|^4583 ≤ (44041654911907/100000000000000 : ℝ)^3559
        have hw : |(5289769609/10000000000 : ℝ)|=(5289769609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361779211/2500000000 : ℝ)|^4583 ≤ (914715908433/2000000000000 : ℝ)^3559
        have hw : |(1361779211/2500000000 : ℝ)|=(1361779211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106350079/625000000 : ℝ)|^4583 ≤ (408901986177/4000000000000 : ℝ)^3559
        have hw : |(-106350079/625000000 : ℝ)|=(106350079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1543_s2_7 (p : ℝ) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253683553/10000000000 : ℝ)*x 0 + (4544209791/10000000000 : ℝ)*x 1 + (994724883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253683553/10000000000 : ℝ)^4583 ≤ (33262357237553/100000000000000 : ℝ)^3559 := by
    have hnat : (4253683553 : ℕ)^4583*100000000000000^3559 ≤ 33262357237553^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253683553 10000000000 33262357237553 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544209791/10000000000 : ℝ)^4583 ≤ (36216115052029/100000000000000 : ℝ)^3559 := by
    have hnat : (4544209791 : ℕ)^4583*100000000000000^3559 ≤ 36216115052029^3559*10000000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544209791 10000000000 36216115052029 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994724883/2500000000 : ℝ)^4583 ≤ (30521527697759/100000000000000 : ℝ)^3559 := by
    have hnat : (994724883 : ℕ)^4583*100000000000000^3559 ≤ 30521527697759^3559*2500000000^4583 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994724883 2500000000 30521527697759 100000000000000 4583 3559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4583/1024 : ℝ)) 4583 3559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253683553/10000000000 : ℝ), (4544209791/10000000000 : ℝ), (994724883/2500000000 : ℝ)] ![(33262357237553/100000000000000 : ℝ), (36216115052029/100000000000000 : ℝ), (30521527697759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253683553/10000000000 : ℝ)|^4583 ≤ (33262357237553/100000000000000 : ℝ)^3559
        have hw : |(4253683553/10000000000 : ℝ)|=(4253683553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544209791/10000000000 : ℝ)|^4583 ≤ (36216115052029/100000000000000 : ℝ)^3559
        have hw : |(4544209791/10000000000 : ℝ)|=(4544209791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(994724883/2500000000 : ℝ)|^4583 ≤ (30521527697759/100000000000000 : ℝ)^3559
        have hw : |(994724883/2500000000 : ℝ)|=(994724883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1543_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8753/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10657/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1589/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8753/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8753/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8753/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8753/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8753/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8753/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8753/100000 : ℝ) ^ (4581/1024 : ℝ) ≤ (57869342283167/3125000000000000000 : ℝ) := by
    have hpowers : (8753/100000 : ℝ)^4581 ≤ (57869342283167/3125000000000000000 : ℝ)^1024 := by
      have hnat : (8753 : ℕ)^4581*3125000000000000000^1024 ≤ 57869342283167^1024*100000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8753 100000 57869342283167 3125000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8753/100000 : ℝ)) (X := (57869342283167/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4503/25000 : ℝ) ^ (4581/1024 : ℝ) ≤ (1168415928631637/2500000000000000000 : ℝ) := by
    have hpowers : (4503/25000 : ℝ)^4581 ≤ (1168415928631637/2500000000000000000 : ℝ)^1024 := by
      have hnat : (4503 : ℕ)^4581*2500000000000000000^1024 ≤ 1168415928631637^1024*25000^4581 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4503 25000 1168415928631637 2500000000000000000 4581 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4503/25000 : ℝ)) (X := (1168415928631637/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562557869342283167/1562500000000000000 : ℝ) ≤ (10000082786961039/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (1562557869342283167/1562500000000000000 : ℝ)^1024 ≤ (10000082786961039/10000000000000000 : ℝ)^4581 := by
      have hnat : (1562557869342283167 : ℕ)^1024*10000000000000000^4581 ≤ 10000082786961039^4581*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562557869342283167 1562500000000000000 10000082786961039 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000082786961039/10000000000000000 : ℝ)) (X := (1562557869342283167/1562500000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506073557012290853/12500000000000000000 : ℝ) ≤ (1250135737819783/1250000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (12506073557012290853/12500000000000000000 : ℝ)^1024 ≤ (1250135737819783/1250000000000000 : ℝ)^4581 := by
      have hnat : (12506073557012290853 : ℕ)^1024*1250000000000000^4581 ≤ 1250135737819783^4581*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506073557012290853 12500000000000000000 1250135737819783 1250000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250135737819783/1250000000000000 : ℝ)) (X := (12506073557012290853/12500000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1251168415928631637/1250000000000000000 : ℝ) ≤ (10002089018155489/10000000000000000 : ℝ) ^ (4581/1024 : ℝ) := by
    have hpowers : (1251168415928631637/1250000000000000000 : ℝ)^1024 ≤ (10002089018155489/10000000000000000 : ℝ)^4581 := by
      have hnat : (1251168415928631637 : ℕ)^1024*10000000000000000^4581 ≤ 10002089018155489^4581*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251168415928631637 1250000000000000000 10002089018155489 10000000000000000 1024 4581 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002089018155489/10000000000000000 : ℝ)) (X := (1251168415928631637/1250000000000000000 : ℝ)) (by norm_num) 4581 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(57869342283167/3125000000000000000 : ℝ) ≤ ((92573205982827239251/92590000000000000000 : ℝ)+2*(40124623889/37036000000000 : ℝ)*(8753/100000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (92573205982827239251/92590000000000000000 : ℝ)+2*(40124623889/37036000000000 : ℝ)*(8753/100000 : ℝ)=(10000082786961039/10000000000000000 : ℝ) by norm_num, show 1+2*(57869342283167/3125000000000000000 : ℝ)=(1562557869342283167/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1168415928631637/2500000000000000000 : ℝ)+(57869342283167/3125000000000000000 : ℝ) ≤ ((92573205982827239251/92590000000000000000 : ℝ)+(40124623889/37036000000000 : ℝ)*((4503/25000 : ℝ)+(8753/100000 : ℝ)))^(4581/1024 : ℝ) := by
    rw [show (92573205982827239251/92590000000000000000 : ℝ)+(40124623889/37036000000000 : ℝ)*((4503/25000 : ℝ)+(8753/100000 : ℝ))=(1250135737819783/1250000000000000 : ℝ) by norm_num, show 1+(1168415928631637/2500000000000000000 : ℝ)+(57869342283167/3125000000000000000 : ℝ)=(12506073557012290853/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1168415928631637/2500000000000000000 : ℝ) ≤ ((92573205982827239251/92590000000000000000 : ℝ)+2*(40124623889/37036000000000 : ℝ)*(4503/25000 : ℝ))^(4581/1024 : ℝ) := by
    rw [show (92573205982827239251/92590000000000000000 : ℝ)+2*(40124623889/37036000000000 : ℝ)*(4503/25000 : ℝ)=(10002089018155489/10000000000000000 : ℝ) by norm_num, show 1+2*(1168415928631637/2500000000000000000 : ℝ)=(1251168415928631637/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92573205982827239251/92590000000000000000 : ℝ)*(X 1 0+X 2 0)+(40124623889/37036000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (8753/100000 : ℝ)) (hi := (4503/25000 : ℝ)) (c := (92573205982827239251/92590000000000000000 : ℝ)) (alpha := (40124623889/37036000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92573205982827239251/92590000000000000000 : ℝ)*(X 0 1+X 2 1)+(40124623889/37036000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (8753/100000 : ℝ)) (hi := (4503/25000 : ℝ)) (c := (92573205982827239251/92590000000000000000 : ℝ)) (alpha := (40124623889/37036000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92573205982827239251/92590000000000000000 : ℝ)*(X 0 2+X 1 2)+(40124623889/37036000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4581/1024 : ℝ)) (lo := (8753/100000 : ℝ)) (hi := (4503/25000 : ℝ)) (c := (92573205982827239251/92590000000000000000 : ℝ)) (alpha := (40124623889/37036000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-910070191/5000000000 : ℝ)*X 0 0+(681078921/1250000000 : ℝ)*X 0 1+(5201653263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354900473/10000000000 : ℝ)*X 1 0+(-1947064651/10000000000 : ℝ)*X 1 1+(5201653193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338724981/2500000000 : ℝ)*X 2 0+(5201653371/10000000000 : ℝ)*X 2 1+(-486766287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((265848691/625000000 : ℝ)*X 0 0+(795078211/2000000000 : ℝ)*X 0 1+(454768841/1000000000 : ℝ)*X 0 2+(265848691/625000000 : ℝ)*X 1 0+(795078211/2000000000 : ℝ)*X 1 1+(454768841/1000000000 : ℝ)*X 1 2+(265848691/625000000 : ℝ)*X 2 0+(795078211/2000000000 : ℝ)*X 2 1+(454768841/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-182018567/1000000000 : ℝ)*X 0 0+(5203154657/10000000000 : ℝ)*X 0 1+(5447116721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289769627/10000000000 : ℝ)*X 1 0+(-106350089/625000000 : ℝ)*X 1 1+(5447116711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289769609/10000000000 : ℝ)*X 2 0+(1361779211/2500000000 : ℝ)*X 2 1+(-106350079/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4253683553/10000000000 : ℝ)*X 0 0+(4544209791/10000000000 : ℝ)*X 0 1+(994724883/2500000000 : ℝ)*X 0 2+(4253683553/10000000000 : ℝ)*X 1 0+(4544209791/10000000000 : ℝ)*X 1 1+(994724883/2500000000 : ℝ)*X 1 2+(4253683553/10000000000 : ℝ)*X 2 0+(4544209791/10000000000 : ℝ)*X 2 1+(994724883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1543_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54155757262938544270230304317/4629500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88756627/6250000000000 : ℝ)*(base19) + (161566323/12500000000000 : ℝ)*(base23) + (236200941/100000000000000 : ℝ)*(upper3) + (39669247/25000000000000 : ℝ)*(lower4) + (2898172053211063/100000000000000 : ℝ)*(major0) + (2898172053211063/100000000000000 : ℝ)*(major1) + (2898172053211063/100000000000000 : ℝ)*(major2) + (126530293931861/3125000000000 : ℝ)*(sp0) + (506123121097781/12500000000000 : ℝ)*(sp1) + (4048984374253267/100000000000000 : ℝ)*(sp2) + (873675035421839/50000000000000 : ℝ)*(sp3) + (2122883591/12500000000000 : ℝ)*(sp4) + (722104429/100000000000000 : ℝ)*(sp6) + (7256757793/100000000000000 : ℝ)*(sp7) + (1747357327601471/100000000000000 : ℝ)*(f.failure) + (101224659722207/2500000000000 : ℝ)*(f.sum) + (2173652175741/1157375000000000000000000000 : ℝ)*base65 + (55828038208196466187/9259000000000000000000000000000000 : ℝ)*base68 + (15219906147361466187/9259000000000000000000000000000000 : ℝ)*base70 + (50717670339540466187/9259000000000000000000000000000000 : ℝ)*base72 + (71349960149/57868750000000000000000000 : ℝ)*base73 + (104105554316561466187/9259000000000000000000000000000000 : ℝ)*base76 + (50850506110775466187/9259000000000000000000000000000000 : ℝ)*base78 + (11496332317755466187/9259000000000000000000000000000000 : ℝ)*base80 + (5682157049721/9259000000000000000000000000 : ℝ)*base82 + (22303113/10000000000000000000000 : ℝ)*base90 + (22303113/10000000000000000000000 : ℝ)*base92 + (22303113/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29048662266413213141291477061/2314750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1886059369/100000000000000 : ℝ)*(base19) + (2093886653/100000000000000 : ℝ)*(base23) + (1804023/800000000000 : ℝ)*(upper3) + (134809/156250000000 : ℝ)*(lower4) + (235970909/100000000000000 : ℝ)*(upper5) + (2933968567023437/100000000000000 : ℝ)*(major0) + (2933968567023437/100000000000000 : ℝ)*(major1) + (2933968567023437/100000000000000 : ℝ)*(major2) + (5125804037/20000000000000 : ℝ)*(sp1) + (30394487293/100000000000000 : ℝ)*(sp2) + (1024749264959069/25000000000000 : ℝ)*(sp4) + (2049484772378361/50000000000000 : ℝ)*(sp5) + (4098964571462331/100000000000000 : ℝ)*(sp6) + (884469827949071/50000000000000 : ℝ)*(sp7) + (884469827949071/50000000000000 : ℝ)*(f.failure) + (1024749264959069/25000000000000 : ℝ)*(f.sum) + (24821373934511/9259000000000000000000000000 : ℝ)*base65 + (2672365848830174313/9259000000000000000000000000000000 : ℝ)*base68 + (5918523898304174313/9259000000000000000000000000000000 : ℝ)*base70 + (34925256656780825687/9259000000000000000000000000000000 : ℝ)*base71 + (1668289614971/2314750000000000000000000000 : ℝ)*base73 + (52958975719513174313/9259000000000000000000000000000000 : ℝ)*base76 + (22425305186227174313/9259000000000000000000000000000000 : ℝ)*base78 + (51048610674195174313/9259000000000000000000000000000000 : ℝ)*base80 + (12298190299699/9259000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (33065913/5000000000000000000000 : ℝ)*base90 + (33065913/5000000000000000000000 : ℝ)*base92 + (33065913/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1543_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8753/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1543_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1543_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1543_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1543_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1543_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4581/1024 : ℝ) ≤ p) (hpb : p ≤ (4583/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165860297/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10657/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1589/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1543_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
