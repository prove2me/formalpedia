-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1304_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:37:22.472561+00:00
-- url     : https://prove2.me/submissions/8455e2d9-d76a-430f-9a3d-3c9d7c31e9bf

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
theorem support_rectangle_w1304_s0_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-366365109/2000000000 : ℝ)*x 0 + (1503372771/2500000000 : ℝ)*x 1 + (4801762223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366365109/2000000000 : ℝ)^533 ≤ (214263939149/2000000000000 : ℝ)^405 := by
    have hnat : (366365109 : ℕ)^533*2000000000000^405 ≤ 214263939149^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366365109 2000000000 214263939149 2000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1503372771/2500000000 : ℝ)^533 ≤ (25602937530417/50000000000000 : ℝ)^405 := by
    have hnat : (1503372771 : ℕ)^533*50000000000000^405 ≤ 25602937530417^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503372771 2500000000 25602937530417 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4801762223/10000000000 : ℝ)^533 ≤ (38080927965083/100000000000000 : ℝ)^405 := by
    have hnat : (4801762223 : ℕ)^533*100000000000000^405 ≤ 38080927965083^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801762223 10000000000 38080927965083 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366365109/2000000000 : ℝ), (1503372771/2500000000 : ℝ), (4801762223/10000000000 : ℝ)] ![(214263939149/2000000000000 : ℝ), (25602937530417/50000000000000 : ℝ), (38080927965083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366365109/2000000000 : ℝ)|^533 ≤ (214263939149/2000000000000 : ℝ)^405
        have hw : |(-366365109/2000000000 : ℝ)|=(366365109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1503372771/2500000000 : ℝ)|^533 ≤ (25602937530417/50000000000000 : ℝ)^405
        have hw : |(1503372771/2500000000 : ℝ)|=(1503372771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4801762223/10000000000 : ℝ)|^533 ≤ (38080927965083/100000000000000 : ℝ)^405
        have hw : |(4801762223/10000000000 : ℝ)|=(4801762223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5506071981/10000000000 : ℝ)*x 0 + (-630623029/2500000000 : ℝ)*x 1 + (1200440551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506071981/10000000000 : ℝ)^533 ≤ (22798439763077/50000000000000 : ℝ)^405 := by
    have hnat : (5506071981 : ℕ)^533*50000000000000^405 ≤ 22798439763077^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506071981 10000000000 22798439763077 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630623029/2500000000 : ℝ)^533 ≤ (8161096345641/50000000000000 : ℝ)^405 := by
    have hnat : (630623029 : ℕ)^533*50000000000000^405 ≤ 8161096345641^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630623029 2500000000 8161096345641 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200440551/2500000000 : ℝ)^533 ≤ (38080927766779/100000000000000 : ℝ)^405 := by
    have hnat : (1200440551 : ℕ)^533*100000000000000^405 ≤ 38080927766779^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200440551 2500000000 38080927766779 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506071981/10000000000 : ℝ), (-630623029/2500000000 : ℝ), (1200440551/2500000000 : ℝ)] ![(22798439763077/50000000000000 : ℝ), (8161096345641/50000000000000 : ℝ), (38080927766779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506071981/10000000000 : ℝ)|^533 ≤ (22798439763077/50000000000000 : ℝ)^405
        have hw : |(5506071981/10000000000 : ℝ)|=(5506071981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-630623029/2500000000 : ℝ)|^533 ≤ (8161096345641/50000000000000 : ℝ)^405
        have hw : |(-630623029/2500000000 : ℝ)|=(630623029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200440551/2500000000 : ℝ)|^533 ≤ (38080927766779/100000000000000 : ℝ)^405
        have hw : |(1200440551/2500000000 : ℝ)|=(1200440551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5506071921/10000000000 : ℝ)*x 0 + (2400881137/5000000000 : ℝ)*x 1 + (-2522492107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506071921/10000000000 : ℝ)^533 ≤ (22798439436123/50000000000000 : ℝ)^405 := by
    have hnat : (5506071921 : ℕ)^533*50000000000000^405 ≤ 22798439436123^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506071921 10000000000 22798439436123 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400881137/5000000000 : ℝ)^533 ≤ (19040464248687/50000000000000 : ℝ)^405 := by
    have hnat : (2400881137 : ℕ)^533*50000000000000^405 ≤ 19040464248687^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400881137 5000000000 19040464248687 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2522492107/10000000000 : ℝ)^533 ≤ (16322192614641/100000000000000 : ℝ)^405 := by
    have hnat : (2522492107 : ℕ)^533*100000000000000^405 ≤ 16322192614641^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522492107 10000000000 16322192614641 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506071921/10000000000 : ℝ), (2400881137/5000000000 : ℝ), (-2522492107/10000000000 : ℝ)] ![(22798439436123/50000000000000 : ℝ), (19040464248687/50000000000000 : ℝ), (16322192614641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506071921/10000000000 : ℝ)|^533 ≤ (22798439436123/50000000000000 : ℝ)^405
        have hw : |(5506071921/10000000000 : ℝ)|=(5506071921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2400881137/5000000000 : ℝ)|^533 ≤ (19040464248687/50000000000000 : ℝ)^405
        have hw : |(2400881137/5000000000 : ℝ)|=(2400881137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2522492107/10000000000 : ℝ)|^533 ≤ (16322192614641/100000000000000 : ℝ)^405
        have hw : |(-2522492107/10000000000 : ℝ)|=(2522492107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (836898533/2000000000 : ℝ)*x 0 + (24286513/78125000 : ℝ)*x 1 + (5610487551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836898533/2000000000 : ℝ)^533 ≤ (635467363027/2000000000000 : ℝ)^405 := by
    have hnat : (836898533 : ℕ)^533*2000000000000^405 ≤ 635467363027^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836898533 2000000000 635467363027 2000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24286513/78125000 : ℝ)^533 ≤ (5372096766671/25000000000000 : ℝ)^405 := by
    have hnat : (24286513 : ℕ)^533*25000000000000^405 ≤ 5372096766671^405*78125000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24286513 78125000 5372096766671 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5610487551/10000000000 : ℝ)^533 ≤ (46738244762357/100000000000000 : ℝ)^405 := by
    have hnat : (5610487551 : ℕ)^533*100000000000000^405 ≤ 46738244762357^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5610487551 10000000000 46738244762357 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836898533/2000000000 : ℝ), (24286513/78125000 : ℝ), (5610487551/10000000000 : ℝ)] ![(635467363027/2000000000000 : ℝ), (5372096766671/25000000000000 : ℝ), (46738244762357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836898533/2000000000 : ℝ)|^533 ≤ (635467363027/2000000000000 : ℝ)^405
        have hw : |(836898533/2000000000 : ℝ)|=(836898533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24286513/78125000 : ℝ)|^533 ≤ (5372096766671/25000000000000 : ℝ)^405
        have hw : |(24286513/78125000 : ℝ)|=(24286513/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5610487551/10000000000 : ℝ)|^533 ≤ (46738244762357/100000000000000 : ℝ)^405
        have hw : |(5610487551/10000000000 : ℝ)|=(5610487551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-367296999/2000000000 : ℝ)*x 0 + (4833014571/10000000000 : ℝ)*x 1 + (5981125219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367296999/2000000000 : ℝ)^533 ≤ (10749073968117/100000000000000 : ℝ)^405 := by
    have hnat : (367296999 : ℕ)^533*100000000000000^405 ≤ 10749073968117^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367296999 2000000000 10749073968117 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4833014571/10000000000 : ℝ)^533 ≤ (38407446240833/100000000000000 : ℝ)^405 := by
    have hnat : (4833014571 : ℕ)^533*100000000000000^405 ≤ 38407446240833^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833014571 10000000000 38407446240833 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5981125219/10000000000 : ℝ)^533 ≤ (12710869944461/25000000000000 : ℝ)^405 := by
    have hnat : (5981125219 : ℕ)^533*25000000000000^405 ≤ 12710869944461^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5981125219 10000000000 12710869944461 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367296999/2000000000 : ℝ), (4833014571/10000000000 : ℝ), (5981125219/10000000000 : ℝ)] ![(10749073968117/100000000000000 : ℝ), (38407446240833/100000000000000 : ℝ), (12710869944461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367296999/2000000000 : ℝ)|^533 ≤ (10749073968117/100000000000000 : ℝ)^405
        have hw : |(-367296999/2000000000 : ℝ)|=(367296999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4833014571/10000000000 : ℝ)|^533 ≤ (38407446240833/100000000000000 : ℝ)^405
        have hw : |(4833014571/10000000000 : ℝ)|=(4833014571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5981125219/10000000000 : ℝ)|^533 ≤ (12710869944461/25000000000000 : ℝ)^405
        have hw : |(5981125219/10000000000 : ℝ)|=(5981125219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5176098457/10000000000 : ℝ)*x 0 + (-268625853/2000000000 : ℝ)*x 1 + (46727541/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176098457/10000000000 : ℝ)^533 ≤ (10508802087933/25000000000000 : ℝ)^405 := by
    have hnat : (5176098457 : ℕ)^533*25000000000000^405 ≤ 10508802087933^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176098457 10000000000 10508802087933 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268625853/2000000000 : ℝ)^533 ≤ (1424262304877/20000000000000 : ℝ)^405 := by
    have hnat : (268625853 : ℕ)^533*20000000000000^405 ≤ 1424262304877^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268625853 2000000000 1424262304877 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46727541/78125000 : ℝ)^533 ≤ (12710870025569/25000000000000 : ℝ)^405 := by
    have hnat : (46727541 : ℕ)^533*25000000000000^405 ≤ 12710870025569^405*78125000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46727541 78125000 12710870025569 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176098457/10000000000 : ℝ), (-268625853/2000000000 : ℝ), (46727541/78125000 : ℝ)] ![(10508802087933/25000000000000 : ℝ), (1424262304877/20000000000000 : ℝ), (12710870025569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176098457/10000000000 : ℝ)|^533 ≤ (10508802087933/25000000000000 : ℝ)^405
        have hw : |(5176098457/10000000000 : ℝ)|=(5176098457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268625853/2000000000 : ℝ)|^533 ≤ (1424262304877/20000000000000 : ℝ)^405
        have hw : |(-268625853/2000000000 : ℝ)|=(268625853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46727541/78125000 : ℝ)|^533 ≤ (12710870025569/25000000000000 : ℝ)^405
        have hw : |(46727541/78125000 : ℝ)|=(46727541/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5176098509/10000000000 : ℝ)*x 0 + (598112519/1000000000 : ℝ)*x 1 + (-1343129279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176098509/10000000000 : ℝ)^533 ≤ (4203520890749/10000000000000 : ℝ)^405 := by
    have hnat : (5176098509 : ℕ)^533*10000000000000^405 ≤ 4203520890749^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176098509 10000000000 4203520890749 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598112519/1000000000 : ℝ)^533 ≤ (50843479453413/100000000000000 : ℝ)^405 := by
    have hnat : (598112519 : ℕ)^533*100000000000000^405 ≤ 50843479453413^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598112519 1000000000 50843479453413 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343129279/10000000000 : ℝ)^533 ≤ (3560655811037/50000000000000 : ℝ)^405 := by
    have hnat : (1343129279 : ℕ)^533*50000000000000^405 ≤ 3560655811037^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343129279 10000000000 3560655811037 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176098509/10000000000 : ℝ), (598112519/1000000000 : ℝ), (-1343129279/10000000000 : ℝ)] ![(4203520890749/10000000000000 : ℝ), (50843479453413/100000000000000 : ℝ), (3560655811037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176098509/10000000000 : ℝ)|^533 ≤ (4203520890749/10000000000000 : ℝ)^405
        have hw : |(5176098509/10000000000 : ℝ)|=(5176098509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598112519/1000000000 : ℝ)|^533 ≤ (50843479453413/100000000000000 : ℝ)^405
        have hw : |(598112519/1000000000 : ℝ)|=(598112519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1343129279/10000000000 : ℝ)|^533 ≤ (3560655811037/50000000000000 : ℝ)^405
        have hw : |(-1343129279/10000000000 : ℝ)|=(1343129279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s0_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4194112569/10000000000 : ℝ)*x 0 + (277298101/500000000 : ℝ)*x 1 + (3175498271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194112569/10000000000 : ℝ)^533 ≤ (3186953403603/10000000000000 : ℝ)^405 := by
    have hnat : (4194112569 : ℕ)^533*10000000000000^405 ≤ 3186953403603^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194112569 10000000000 3186953403603 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277298101/500000000 : ℝ)^533 ≤ (46032116701381/100000000000000 : ℝ)^405 := by
    have hnat : (277298101 : ℕ)^533*100000000000000^405 ≤ 46032116701381^405*500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277298101 500000000 46032116701381 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3175498271/10000000000 : ℝ)^533 ≤ (22098349248283/100000000000000 : ℝ)^405 := by
    have hnat : (3175498271 : ℕ)^533*100000000000000^405 ≤ 22098349248283^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3175498271 10000000000 22098349248283 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194112569/10000000000 : ℝ), (277298101/500000000 : ℝ), (3175498271/10000000000 : ℝ)] ![(3186953403603/10000000000000 : ℝ), (46032116701381/100000000000000 : ℝ), (22098349248283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194112569/10000000000 : ℝ)|^533 ≤ (3186953403603/10000000000000 : ℝ)^405
        have hw : |(4194112569/10000000000 : ℝ)|=(4194112569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277298101/500000000 : ℝ)|^533 ≤ (46032116701381/100000000000000 : ℝ)^405
        have hw : |(277298101/500000000 : ℝ)|=(277298101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3175498271/10000000000 : ℝ)|^533 ≤ (22098349248283/100000000000000 : ℝ)^405
        have hw : |(3175498271/10000000000 : ℝ)|=(3175498271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (9/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27147/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4263/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4263 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4263*1^1024 ≤ 0^1024*1^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4263/1024 : ℝ) ≤ (275582451349500599/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4263 ≤ (275582451349500599/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4263*12500000000000000000^1024 ≤ 275582451349500599^1024*5^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 275582451349500599 12500000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (275582451349500599/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4263 := by
      have hnat : (1 : ℕ)^1024*1^4263 ≤ 1^4263*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12775582451349500599/12500000000000000000 : ℝ) ≤ (10052519450570977/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (12775582451349500599/12500000000000000000 : ℝ)^1024 ≤ (10052519450570977/10000000000000000 : ℝ)^4263 := by
      have hnat : (12775582451349500599 : ℕ)^1024*10000000000000000^4263 ≤ 10052519450570977^4263*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12775582451349500599 12500000000000000000 10052519450570977 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052519450570977/10000000000000000 : ℝ)) (X := (12775582451349500599/12500000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6525582451349500599/6250000000000000000 : ℝ) ≤ (5052519450570977/5000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (6525582451349500599/6250000000000000000 : ℝ)^1024 ≤ (5052519450570977/5000000000000000 : ℝ)^4263 := by
      have hnat : (6525582451349500599 : ℕ)^1024*5000000000000000^4263 ≤ 5052519450570977^4263*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6525582451349500599 6250000000000000000 5052519450570977 5000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5052519450570977/5000000000000000 : ℝ)) (X := (6525582451349500599/6250000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(52519450570977/4000000000000000 : ℝ)*(0 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(52519450570977/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(275582451349500599/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(52519450570977/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (1 : ℝ)+(52519450570977/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10052519450570977/10000000000000000 : ℝ) by norm_num, show 1+(275582451349500599/12500000000000000000 : ℝ)+(0 : ℝ)=(12775582451349500599/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(275582451349500599/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(52519450570977/4000000000000000 : ℝ)*(2/5 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(52519450570977/4000000000000000 : ℝ)*(2/5 : ℝ)=(5052519450570977/5000000000000000 : ℝ) by norm_num, show 1+2*(275582451349500599/12500000000000000000 : ℝ)=(6525582451349500599/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(52519450570977/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52519450570977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(52519450570977/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52519450570977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(52519450570977/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52519450570977/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-366365109/2000000000 : ℝ)*X 0 0+(1503372771/2500000000 : ℝ)*X 0 1+(4801762223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5506071981/10000000000 : ℝ)*X 1 0+(-630623029/2500000000 : ℝ)*X 1 1+(1200440551/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5506071921/10000000000 : ℝ)*X 2 0+(2400881137/5000000000 : ℝ)*X 2 1+(-2522492107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((836898533/2000000000 : ℝ)*X 0 0+(24286513/78125000 : ℝ)*X 0 1+(5610487551/10000000000 : ℝ)*X 0 2+(836898533/2000000000 : ℝ)*X 1 0+(24286513/78125000 : ℝ)*X 1 1+(5610487551/10000000000 : ℝ)*X 1 2+(836898533/2000000000 : ℝ)*X 2 0+(24286513/78125000 : ℝ)*X 2 1+(5610487551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-367296999/2000000000 : ℝ)*X 0 0+(4833014571/10000000000 : ℝ)*X 0 1+(5981125219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5176098457/10000000000 : ℝ)*X 1 0+(-268625853/2000000000 : ℝ)*X 1 1+(46727541/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5176098509/10000000000 : ℝ)*X 2 0+(598112519/1000000000 : ℝ)*X 2 1+(-1343129279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4194112569/10000000000 : ℝ)*X 0 0+(277298101/500000000 : ℝ)*X 0 1+(3175498271/10000000000 : ℝ)*X 0 2+(4194112569/10000000000 : ℝ)*X 1 0+(277298101/500000000 : ℝ)*X 1 1+(3175498271/10000000000 : ℝ)*X 1 2+(4194112569/10000000000 : ℝ)*X 2 0+(277298101/500000000 : ℝ)*X 2 1+(3175498271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120089085307816939729431/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1777017/2500000000000 : ℝ)*(base1) + (291887359/20000000000000 : ℝ)*(base19) + (725221863/50000000000000 : ℝ)*(base23) + (170990083/100000000000000 : ℝ)*(upper3) + (21285503/12500000000000 : ℝ)*(upper5) + (306247701301501/50000000000000 : ℝ)*(major0) + (306247701301501/50000000000000 : ℝ)*(major1) + (306247701301501/50000000000000 : ℝ)*(major2) + (825271579812337/100000000000000 : ℝ)*(sp0) + (825274729453499/100000000000000 : ℝ)*(sp1) + (103159342305821/12500000000000 : ℝ)*(sp2) + (399712109751339/100000000000000 : ℝ)*(sp3) + (4680158637/100000000000000 : ℝ)*(sp4) + (223533521/10000000000000 : ℝ)*(sp7) + (99928604041807/25000000000000 : ℝ)*(f.failure) + (412638094445147/50000000000000 : ℝ)*(f.sum) + (181137767363523/100000000000000000000000000000 : ℝ)*base66 + (473952189063523/200000000000000000000000000000 : ℝ)*base68 + (1198122393463523/200000000000000000000000000000 : ℝ)*base70 + (388558411663523/200000000000000000000000000000 : ℝ)*base72 + (244624164063523/100000000000000000000000000000 : ℝ)*base74 + (229410421863523/200000000000000000000000000000 : ℝ)*base76 + (576019533463523/200000000000000000000000000000 : ℝ)*base78 + (39653291536477/200000000000000000000000000000 : ℝ)*base79 + (529985915163523/100000000000000000000000000000 : ℝ)*base82 + (15391829/2500000000000000000000 : ℝ)*base90 + (15391829/2500000000000000000000 : ℝ)*base92 + (15391829/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454724029273157259/100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1070694003/100000000000000 : ℝ)*(base19) + (43422019/4000000000000 : ℝ)*(base23) + (51662117/100000000000000 : ℝ)*(base32) + (150035109/100000000000000 : ℝ)*(upper3) + (4608167/4000000000000 : ℝ)*(upper5) + (323213611509301/50000000000000 : ℝ)*(major0) + (323213611509301/50000000000000 : ℝ)*(major1) + (323213611509301/50000000000000 : ℝ)*(major2) + (599453431/25000000000000 : ℝ)*(sp1) + (99744021/4000000000000 : ℝ)*(sp2) + (435497988460937/50000000000000 : ℝ)*(sp4) + (435496254207073/50000000000000 : ℝ)*(sp5) + (435496198885437/50000000000000 : ℝ)*(sp6) + (421858265878529/100000000000000 : ℝ)*(sp7) + (421858317540647/100000000000000 : ℝ)*(f.failure) + (435497988460937/50000000000000 : ℝ)*(f.sum) + (254878159057077/100000000000000000000000000000 : ℝ)*base65 + (789044269357077/200000000000000000000000000000 : ℝ)*base67 + (2245269556842923/200000000000000000000000000000 : ℝ)*base70 + (835189002757077/200000000000000000000000000000 : ℝ)*base71 + (585834605557077/100000000000000000000000000000 : ℝ)*base73 + (373770656442923/200000000000000000000000000000 : ℝ)*base76 + (510240082242923/200000000000000000000000000000 : ℝ)*base78 + (197092501842923/200000000000000000000000000000 : ℝ)*base80 + (264251537642923/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (99534691/10000000000000000000000 : ℝ)*base89 + (99534691/10000000000000000000000 : ℝ)*base91 + (99534691/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1304_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27147/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1304_s1_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-404426899/2000000000 : ℝ)*x 0 + (707451369/1250000000 : ℝ)*x 1 + (5033797803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404426899/2000000000 : ℝ)^533 ≤ (6100728991147/50000000000000 : ℝ)^405 := by
    have hnat : (404426899 : ℕ)^533*50000000000000^405 ≤ 6100728991147^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404426899 2000000000 6100728991147 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707451369/1250000000 : ℝ)^533 ≤ (11819386585563/25000000000000 : ℝ)^405 := by
    have hnat : (707451369 : ℕ)^533*25000000000000^405 ≤ 11819386585563^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707451369 1250000000 11819386585563 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033797803/10000000000 : ℝ)^533 ≤ (40520995654347/100000000000000 : ℝ)^405 := by
    have hnat : (5033797803 : ℕ)^533*100000000000000^405 ≤ 40520995654347^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033797803 10000000000 40520995654347 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404426899/2000000000 : ℝ), (707451369/1250000000 : ℝ), (5033797803/10000000000 : ℝ)] ![(6100728991147/50000000000000 : ℝ), (11819386585563/25000000000000 : ℝ), (40520995654347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404426899/2000000000 : ℝ)|^533 ≤ (6100728991147/50000000000000 : ℝ)^405
        have hw : |(-404426899/2000000000 : ℝ)|=(404426899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707451369/1250000000 : ℝ)|^533 ≤ (11819386585563/25000000000000 : ℝ)^405
        have hw : |(707451369/1250000000 : ℝ)|=(707451369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5033797803/10000000000 : ℝ)|^533 ≤ (40520995654347/100000000000000 : ℝ)^405
        have hw : |(5033797803/10000000000 : ℝ)|=(5033797803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5409711723/10000000000 : ℝ)*x 0 + (-471439353/2000000000 : ℝ)*x 1 + (5033798047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409711723/10000000000 : ℝ)^533 ≤ (1392175512621/3125000000000 : ℝ)^405 := by
    have hnat : (5409711723 : ℕ)^533*3125000000000^405 ≤ 1392175512621^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409711723 10000000000 1392175512621 3125000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471439353/2000000000 : ℝ)^533 ≤ (7464692673723/50000000000000 : ℝ)^405 := by
    have hnat : (471439353 : ℕ)^533*50000000000000^405 ≤ 7464692673723^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471439353 2000000000 7464692673723 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033798047/10000000000 : ℝ)^533 ≤ (20260499119631/50000000000000 : ℝ)^405 := by
    have hnat : (5033798047 : ℕ)^533*50000000000000^405 ≤ 20260499119631^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033798047 10000000000 20260499119631 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409711723/10000000000 : ℝ), (-471439353/2000000000 : ℝ), (5033798047/10000000000 : ℝ)] ![(1392175512621/3125000000000 : ℝ), (7464692673723/50000000000000 : ℝ), (20260499119631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409711723/10000000000 : ℝ)|^533 ≤ (1392175512621/3125000000000 : ℝ)^405
        have hw : |(5409711723/10000000000 : ℝ)|=(5409711723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471439353/2000000000 : ℝ)|^533 ≤ (7464692673723/50000000000000 : ℝ)^405
        have hw : |(-471439353/2000000000 : ℝ)|=(471439353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5033798047/10000000000 : ℝ)|^533 ≤ (20260499119631/50000000000000 : ℝ)^405
        have hw : |(5033798047/10000000000 : ℝ)|=(5033798047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5409712001/10000000000 : ℝ)*x 0 + (2516898799/5000000000 : ℝ)*x 1 + (-2357196973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409712001/10000000000 : ℝ)^533 ≤ (22274809708393/50000000000000 : ℝ)^405 := by
    have hnat : (5409712001 : ℕ)^533*50000000000000^405 ≤ 22274809708393^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409712001 10000000000 22274809708393 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516898799/5000000000 : ℝ)^533 ≤ (20260496741297/50000000000000 : ℝ)^405 := by
    have hnat : (2516898799 : ℕ)^533*50000000000000^405 ≤ 20260496741297^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516898799 5000000000 20260496741297 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2357196973/10000000000 : ℝ)^533 ≤ (1866173385147/12500000000000 : ℝ)^405 := by
    have hnat : (2357196973 : ℕ)^533*12500000000000^405 ≤ 1866173385147^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357196973 10000000000 1866173385147 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409712001/10000000000 : ℝ), (2516898799/5000000000 : ℝ), (-2357196973/10000000000 : ℝ)] ![(22274809708393/50000000000000 : ℝ), (20260496741297/50000000000000 : ℝ), (1866173385147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409712001/10000000000 : ℝ)|^533 ≤ (22274809708393/50000000000000 : ℝ)^405
        have hw : |(5409712001/10000000000 : ℝ)|=(5409712001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516898799/5000000000 : ℝ)|^533 ≤ (20260496741297/50000000000000 : ℝ)^405
        have hw : |(2516898799/5000000000 : ℝ)|=(2516898799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2357196973/10000000000 : ℝ)|^533 ≤ (1866173385147/12500000000000 : ℝ)^405
        have hw : |(-2357196973/10000000000 : ℝ)|=(2357196973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (268689699/625000000 : ℝ)*x 0 + (3698731817/10000000000 : ℝ)*x 1 + (1247706547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268689699/625000000 : ℝ)^533 ≤ (16461451792451/50000000000000 : ℝ)^405 := by
    have hnat : (268689699 : ℕ)^533*50000000000000^405 ≤ 16461451792451^405*625000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268689699 625000000 16461451792451 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3698731817/10000000000 : ℝ)^533 ≤ (13505361553841/50000000000000 : ℝ)^405 := by
    have hnat : (3698731817 : ℕ)^533*50000000000000^405 ≤ 13505361553841^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698731817 10000000000 13505361553841 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1247706547/2500000000 : ℝ)^533 ≤ (40066373286273/100000000000000 : ℝ)^405 := by
    have hnat : (1247706547 : ℕ)^533*100000000000000^405 ≤ 40066373286273^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247706547 2500000000 40066373286273 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268689699/625000000 : ℝ), (3698731817/10000000000 : ℝ), (1247706547/2500000000 : ℝ)] ![(16461451792451/50000000000000 : ℝ), (13505361553841/50000000000000 : ℝ), (40066373286273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268689699/625000000 : ℝ)|^533 ≤ (16461451792451/50000000000000 : ℝ)^405
        have hw : |(268689699/625000000 : ℝ)|=(268689699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3698731817/10000000000 : ℝ)|^533 ≤ (13505361553841/50000000000000 : ℝ)^405
        have hw : |(3698731817/10000000000 : ℝ)|=(3698731817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1247706547/2500000000 : ℝ)|^533 ≤ (40066373286273/100000000000000 : ℝ)^405
        have hw : |(1247706547/2500000000 : ℝ)|=(1247706547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022745947/10000000000 : ℝ)*x 0 + (5041882711/10000000000 : ℝ)*x 1 + (565137443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022745947/10000000000 : ℝ)^533 ≤ (6103156869937/50000000000000 : ℝ)^405 := by
    have hnat : (2022745947 : ℕ)^533*50000000000000^405 ≤ 6103156869937^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022745947 10000000000 6103156869937 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5041882711/10000000000 : ℝ)^533 ≤ (203033341109/500000000000 : ℝ)^405 := by
    have hnat : (5041882711 : ℕ)^533*500000000000^405 ≤ 203033341109^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5041882711 10000000000 203033341109 500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565137443/1000000000 : ℝ)^533 ≤ (47187018018823/100000000000000 : ℝ)^405 := by
    have hnat : (565137443 : ℕ)^533*100000000000000^405 ≤ 47187018018823^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565137443 1000000000 47187018018823 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022745947/10000000000 : ℝ), (5041882711/10000000000 : ℝ), (565137443/1000000000 : ℝ)] ![(6103156869937/50000000000000 : ℝ), (203033341109/500000000000 : ℝ), (47187018018823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022745947/10000000000 : ℝ)|^533 ≤ (6103156869937/50000000000000 : ℝ)^405
        have hw : |(-2022745947/10000000000 : ℝ)|=(2022745947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5041882711/10000000000 : ℝ)|^533 ≤ (203033341109/500000000000 : ℝ)^405
        have hw : |(5041882711/10000000000 : ℝ)|=(5041882711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565137443/1000000000 : ℝ)|^533 ≤ (47187018018823/100000000000000 : ℝ)^405
        have hw : |(565137443/1000000000 : ℝ)|=(565137443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5247851129/10000000000 : ℝ)*x 0 + (-1739619523/10000000000 : ℝ)*x 1 + (1412843803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247851129/10000000000 : ℝ)^533 ≤ (42803751538013/100000000000000 : ℝ)^405 := by
    have hnat : (5247851129 : ℕ)^533*100000000000000^405 ≤ 42803751538013^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247851129 10000000000 42803751538013 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1739619523/10000000000 : ℝ)^533 ≤ (10009221836853/100000000000000 : ℝ)^405 := by
    have hnat : (1739619523 : ℕ)^533*100000000000000^405 ≤ 10009221836853^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739619523 10000000000 10009221836853 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1412843803/2500000000 : ℝ)^533 ≤ (23593513305937/50000000000000 : ℝ)^405 := by
    have hnat : (1412843803 : ℕ)^533*50000000000000^405 ≤ 23593513305937^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412843803 2500000000 23593513305937 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247851129/10000000000 : ℝ), (-1739619523/10000000000 : ℝ), (1412843803/2500000000 : ℝ)] ![(42803751538013/100000000000000 : ℝ), (10009221836853/100000000000000 : ℝ), (23593513305937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247851129/10000000000 : ℝ)|^533 ≤ (42803751538013/100000000000000 : ℝ)^405
        have hw : |(5247851129/10000000000 : ℝ)|=(5247851129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1739619523/10000000000 : ℝ)|^533 ≤ (10009221836853/100000000000000 : ℝ)^405
        have hw : |(-1739619523/10000000000 : ℝ)|=(1739619523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1412843803/2500000000 : ℝ)|^533 ≤ (23593513305937/50000000000000 : ℝ)^405
        have hw : |(1412843803/2500000000 : ℝ)|=(1412843803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (104957021/200000000 : ℝ)*x 0 + (1412843699/2500000000 : ℝ)*x 1 + (-1739620239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104957021/200000000 : ℝ)^533 ≤ (21401875345003/50000000000000 : ℝ)^405 := by
    have hnat : (104957021 : ℕ)^533*50000000000000^405 ≤ 21401875345003^405*200000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104957021 200000000 21401875345003 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1412843699/2500000000 : ℝ)^533 ≤ (9437404408127/20000000000000 : ℝ)^405 := by
    have hnat : (1412843699 : ℕ)^533*20000000000000^405 ≤ 9437404408127^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412843699 2500000000 9437404408127 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739620239/10000000000 : ℝ)^533 ≤ (20018454517/200000000000 : ℝ)^405 := by
    have hnat : (1739620239 : ℕ)^533*200000000000^405 ≤ 20018454517^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739620239 10000000000 20018454517 200000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104957021/200000000 : ℝ), (1412843699/2500000000 : ℝ), (-1739620239/10000000000 : ℝ)] ![(21401875345003/50000000000000 : ℝ), (9437404408127/20000000000000 : ℝ), (20018454517/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104957021/200000000 : ℝ)|^533 ≤ (21401875345003/50000000000000 : ℝ)^405
        have hw : |(104957021/200000000 : ℝ)|=(104957021/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1412843699/2500000000 : ℝ)|^533 ≤ (9437404408127/20000000000000 : ℝ)^405
        have hw : |(1412843699/2500000000 : ℝ)|=(1412843699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1739620239/10000000000 : ℝ)|^533 ≤ (20018454517/200000000000 : ℝ)^405
        have hw : |(-1739620239/10000000000 : ℝ)|=(1739620239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s1_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1075074169/2500000000 : ℝ)*x 0 + (2487067077/5000000000 : ℝ)*x 1 + (464467087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075074169/2500000000 : ℝ)^533 ≤ (32935618221551/100000000000000 : ℝ)^405 := by
    have hnat : (1075074169 : ℕ)^533*100000000000000^405 ≤ 32935618221551^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075074169 2500000000 32935618221551 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2487067077/5000000000 : ℝ)^533 ≤ (19945055527279/50000000000000 : ℝ)^405 := by
    have hnat : (2487067077 : ℕ)^533*50000000000000^405 ≤ 19945055527279^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487067077 5000000000 19945055527279 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464467087/1250000000 : ℝ)^533 ≤ (6793567677107/25000000000000 : ℝ)^405 := by
    have hnat : (464467087 : ℕ)^533*25000000000000^405 ≤ 6793567677107^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464467087 1250000000 6793567677107 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075074169/2500000000 : ℝ), (2487067077/5000000000 : ℝ), (464467087/1250000000 : ℝ)] ![(32935618221551/100000000000000 : ℝ), (19945055527279/50000000000000 : ℝ), (6793567677107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075074169/2500000000 : ℝ)|^533 ≤ (32935618221551/100000000000000 : ℝ)^405
        have hw : |(1075074169/2500000000 : ℝ)|=(1075074169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2487067077/5000000000 : ℝ)|^533 ≤ (19945055527279/50000000000000 : ℝ)^405
        have hw : |(2487067077/5000000000 : ℝ)|=(2487067077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464467087/1250000000 : ℝ)|^533 ≤ (6793567677107/25000000000000 : ℝ)^405
        have hw : |(464467087/1250000000 : ℝ)|=(464467087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27147/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/800 : ℝ)*pair X i i ≤ pair X i h) :
    (6527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9877/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27147/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27147/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27147/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27147/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27147/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27147/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9/800 : ℝ) ^ (4263/1024 : ℝ) ≤ (48157118097/6250000000000000000 : ℝ) := by
    have hpowers : (9/800 : ℝ)^4263 ≤ (48157118097/6250000000000000000 : ℝ)^1024 := by
      have hnat : (9 : ℕ)^4263*6250000000000000000^1024 ≤ 48157118097^1024*800^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 800 48157118097 6250000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/800 : ℝ)) (X := (48157118097/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27147/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (439071620820743671/100000000000000000000 : ℝ) := by
    have hpowers : (27147/100000 : ℝ)^4263 ≤ (439071620820743671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27147 : ℕ)^4263*100000000000000000000^1024 ≤ 439071620820743671^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27147 100000 439071620820743671 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27147/100000 : ℝ)) (X := (439071620820743671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000048157118097/3125000000000000000 : ℝ) ≤ (5000000018508239/5000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (3125000048157118097/3125000000000000000 : ℝ)^1024 ≤ (5000000018508239/5000000000000000 : ℝ)^4263 := by
      have hnat : (3125000048157118097 : ℕ)^1024*5000000000000000^4263 ≤ 5000000018508239^4263*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000048157118097 3125000000000000000 5000000018508239 5000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000018508239/5000000000000000 : ℝ)) (X := (3125000048157118097/3125000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100439072391334633223/100000000000000000000 : ℝ) ≤ (10010529253927729/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (100439072391334633223/100000000000000000000 : ℝ)^1024 ≤ (10010529253927729/10000000000000000 : ℝ)^4263 := by
      have hnat : (100439072391334633223 : ℕ)^1024*10000000000000000^4263 ≤ 10010529253927729^4263*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100439072391334633223 100000000000000000000 10010529253927729 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010529253927729/10000000000000000 : ℝ)) (X := (100439072391334633223/100000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50439071620820743671/50000000000000000000 : ℝ) ≤ (501052923541949/500000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50439071620820743671/50000000000000000000 : ℝ)^1024 ≤ (501052923541949/500000000000000 : ℝ)^4263 := by
      have hnat : (50439071620820743671 : ℕ)^1024*500000000000000^4263 ≤ 501052923541949^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50439071620820743671 50000000000000000000 501052923541949 500000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501052923541949/500000000000000 : ℝ)) (X := (50439071620820743671/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48157118097/6250000000000000000 : ℝ) ≤ ((43366051704198745961/43370000000000000000 : ℝ)+2*(3509738970417/867400000000000 : ℝ)*(9/800 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (43366051704198745961/43370000000000000000 : ℝ)+2*(3509738970417/867400000000000 : ℝ)*(9/800 : ℝ)=(5000000018508239/5000000000000000 : ℝ) by norm_num, show 1+2*(48157118097/6250000000000000000 : ℝ)=(3125000048157118097/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(439071620820743671/100000000000000000000 : ℝ)+(48157118097/6250000000000000000 : ℝ) ≤ ((43366051704198745961/43370000000000000000 : ℝ)+(3509738970417/867400000000000 : ℝ)*((27147/100000 : ℝ)+(9/800 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (43366051704198745961/43370000000000000000 : ℝ)+(3509738970417/867400000000000 : ℝ)*((27147/100000 : ℝ)+(9/800 : ℝ))=(10010529253927729/10000000000000000 : ℝ) by norm_num, show 1+(439071620820743671/100000000000000000000 : ℝ)+(48157118097/6250000000000000000 : ℝ)=(100439072391334633223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(439071620820743671/100000000000000000000 : ℝ) ≤ ((43366051704198745961/43370000000000000000 : ℝ)+2*(3509738970417/867400000000000 : ℝ)*(27147/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (43366051704198745961/43370000000000000000 : ℝ)+2*(3509738970417/867400000000000 : ℝ)*(27147/100000 : ℝ)=(501052923541949/500000000000000 : ℝ) by norm_num, show 1+2*(439071620820743671/100000000000000000000 : ℝ)=(50439071620820743671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43366051704198745961/43370000000000000000 : ℝ)*(X 1 0+X 2 0)+(3509738970417/867400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (9/800 : ℝ)) (hi := (27147/100000 : ℝ)) (c := (43366051704198745961/43370000000000000000 : ℝ)) (alpha := (3509738970417/867400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43366051704198745961/43370000000000000000 : ℝ)*(X 0 1+X 2 1)+(3509738970417/867400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (9/800 : ℝ)) (hi := (27147/100000 : ℝ)) (c := (43366051704198745961/43370000000000000000 : ℝ)) (alpha := (3509738970417/867400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43366051704198745961/43370000000000000000 : ℝ)*(X 0 2+X 1 2)+(3509738970417/867400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (9/800 : ℝ)) (hi := (27147/100000 : ℝ)) (c := (43366051704198745961/43370000000000000000 : ℝ)) (alpha := (3509738970417/867400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404426899/2000000000 : ℝ)*X 0 0+(707451369/1250000000 : ℝ)*X 0 1+(5033797803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5409711723/10000000000 : ℝ)*X 1 0+(-471439353/2000000000 : ℝ)*X 1 1+(5033798047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5409712001/10000000000 : ℝ)*X 2 0+(2516898799/5000000000 : ℝ)*X 2 1+(-2357196973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((268689699/625000000 : ℝ)*X 0 0+(3698731817/10000000000 : ℝ)*X 0 1+(1247706547/2500000000 : ℝ)*X 0 2+(268689699/625000000 : ℝ)*X 1 0+(3698731817/10000000000 : ℝ)*X 1 1+(1247706547/2500000000 : ℝ)*X 1 2+(268689699/625000000 : ℝ)*X 2 0+(3698731817/10000000000 : ℝ)*X 2 1+(1247706547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2022745947/10000000000 : ℝ)*X 0 0+(5041882711/10000000000 : ℝ)*X 0 1+(565137443/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247851129/10000000000 : ℝ)*X 1 0+(-1739619523/10000000000 : ℝ)*X 1 1+(1412843803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((104957021/200000000 : ℝ)*X 2 0+(1412843699/2500000000 : ℝ)*X 2 1+(-1739620239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075074169/2500000000 : ℝ)*X 0 0+(2487067077/5000000000 : ℝ)*X 0 1+(464467087/1250000000 : ℝ)*X 0 2+(1075074169/2500000000 : ℝ)*X 1 0+(2487067077/5000000000 : ℝ)*X 1 1+(464467087/1250000000 : ℝ)*X 1 2+(1075074169/2500000000 : ℝ)*X 2 0+(2487067077/5000000000 : ℝ)*X 2 1+(464467087/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123354250495726156337633229/16941406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (73792761/100000000000000 : ℝ)*(base1) + (159853533/12500000000000 : ℝ)*(base19) + (1360944601/100000000000000 : ℝ)*(base23) + (98036351/50000000000000 : ℝ)*(upper3) + (134514209/100000000000000 : ℝ)*(upper5) + (1158144585111/97656250000 : ℝ)*(major0) + (1158144585111/97656250000 : ℝ)*(major1) + (1158144585111/97656250000 : ℝ)*(major2) + (1597928484616621/100000000000000 : ℝ)*(sp0) + (399483567648223/25000000000000 : ℝ)*(sp1) + (319586837695311/20000000000000 : ℝ)*(sp2) + (48371283004751/6250000000000 : ℝ)*(sp3) + (7138597297/100000000000000 : ℝ)*(sp4) + (1858154887/50000000000000 : ℝ)*(sp7) + (773944318178551/100000000000000 : ℝ)*(f.failure) + (399483887355289/25000000000000 : ℝ)*(f.sum) + (6863971698927/10842500000000000000000000000 : ℝ)*base65 + (315951403382035139/67765625000000000000000000000000 : ℝ)*base68 + (186531627309316389/67765625000000000000000000000000 : ℝ)*base70 + (23447880818200191/16941406250000000000000000000000 : ℝ)*base72 + (1085679385771/1355312500000000000000000000 : ℝ)*base74 + (74300229017643559/16941406250000000000000000000000 : ℝ)*base75 + (348191900128089861/67765625000000000000000000000000 : ℝ)*base77 + (75635369003103507/33882812500000000000000000000000 : ℝ)*base80 + (32103938539499/21685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4556403/10000000000000000000000 : ℝ)*base89 + (4556403/10000000000000000000000 : ℝ)*base91 + (4556403/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (612032356107458374494760443/216850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394901341/100000000000000 : ℝ)*(base19) + (453576829/100000000000000 : ℝ)*(base23) + (59119999/100000000000000 : ℝ)*(upper2) + (15125531/12500000000000 : ℝ)*(upper3) + (54028943/100000000000000 : ℝ)*(upper5) + (121768587600321/10000000000000 : ℝ)*(major0) + (121768587600321/10000000000000 : ℝ)*(major1) + (121768587600321/10000000000000 : ℝ)*(major2) + (1449430633/50000000000000 : ℝ)*(sp1) + (1949498611/100000000000000 : ℝ)*(sp2) + (820355010696883/50000000000000 : ℝ)*(sp4) + (1640706727631159/100000000000000 : ℝ)*(sp5) + (820353809159163/50000000000000 : ℝ)*(sp6) + (79466163653343/10000000000000 : ℝ)*(sp7) + (79466163653343/10000000000000 : ℝ)*(f.failure) + (820355010696883/50000000000000 : ℝ)*(f.sum) + (25857103645829/4337000000000000000000000000 : ℝ)*base66 + (2863341173136296519/433700000000000000000000000000000 : ℝ)*base68 + (1449480393568096519/433700000000000000000000000000000 : ℝ)*base70 + (3974905886679396519/433700000000000000000000000000000 : ℝ)*base72 + (2629212420811/1084250000000000000000000000 : ℝ)*base74 + (878458642660903481/433700000000000000000000000000000 : ℝ)*base75 + (4368845607342796519/433700000000000000000000000000000 : ℝ)*base78 + (650119667706103481/433700000000000000000000000000000 : ℝ)*base79 + (3147990303513/2168500000000000000000000000 : ℝ)*base81 + (12214779/1000000000000000000000 : ℝ)*base89 + (12214779/1000000000000000000000 : ℝ)*base91 + (12214779/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1304_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27147/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9877/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1304_s2_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065706641/10000000000 : ℝ)*x 0 + (1098122583/2000000000 : ℝ)*x 1 + (5174945841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065706641/10000000000 : ℝ)^533 ≤ (12548635773327/100000000000000 : ℝ)^405 := by
    have hnat : (2065706641 : ℕ)^533*100000000000000^405 ≤ 12548635773327^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065706641 10000000000 12548635773327 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098122583/2000000000 : ℝ)^533 ≤ (22714237100107/50000000000000 : ℝ)^405 := by
    have hnat : (1098122583 : ℕ)^533*50000000000000^405 ≤ 22714237100107^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098122583 2000000000 22714237100107 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174945841/10000000000 : ℝ)^533 ≤ (2626430625671/6250000000000 : ℝ)^405 := by
    have hnat : (5174945841 : ℕ)^533*6250000000000^405 ≤ 2626430625671^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174945841 10000000000 2626430625671 6250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065706641/10000000000 : ℝ), (1098122583/2000000000 : ℝ), (5174945841/10000000000 : ℝ)] ![(12548635773327/100000000000000 : ℝ), (22714237100107/50000000000000 : ℝ), (2626430625671/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065706641/10000000000 : ℝ)|^533 ≤ (12548635773327/100000000000000 : ℝ)^405
        have hw : |(-2065706641/10000000000 : ℝ)|=(2065706641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098122583/2000000000 : ℝ)|^533 ≤ (22714237100107/50000000000000 : ℝ)^405
        have hw : |(1098122583/2000000000 : ℝ)|=(1098122583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174945841/10000000000 : ℝ)|^533 ≤ (2626430625671/6250000000000 : ℝ)^405
        have hw : |(5174945841/10000000000 : ℝ)|=(5174945841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (536869073/1000000000 : ℝ)*x 0 + (-557292939/2500000000 : ℝ)*x 1 + (1293736403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536869073/1000000000 : ℝ)^533 ≤ (2205278590823/5000000000000 : ℝ)^405 := by
    have hnat : (536869073 : ℕ)^533*5000000000000^405 ≤ 2205278590823^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536869073 1000000000 2205278590823 5000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557292939/2500000000 : ℝ)^533 ≤ (13871540603639/100000000000000 : ℝ)^405 := by
    have hnat : (557292939 : ℕ)^533*100000000000000^405 ≤ 13871540603639^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557292939 2500000000 13871540603639 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293736403/2500000000 : ℝ)^533 ≤ (42022887563433/100000000000000 : ℝ)^405 := by
    have hnat : (1293736403 : ℕ)^533*100000000000000^405 ≤ 42022887563433^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293736403 2500000000 42022887563433 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536869073/1000000000 : ℝ), (-557292939/2500000000 : ℝ), (1293736403/2500000000 : ℝ)] ![(2205278590823/5000000000000 : ℝ), (13871540603639/100000000000000 : ℝ), (42022887563433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536869073/1000000000 : ℝ)|^533 ≤ (2205278590823/5000000000000 : ℝ)^405
        have hw : |(536869073/1000000000 : ℝ)|=(536869073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557292939/2500000000 : ℝ)|^533 ≤ (13871540603639/100000000000000 : ℝ)^405
        have hw : |(-557292939/2500000000 : ℝ)|=(557292939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293736403/2500000000 : ℝ)|^533 ≤ (42022887563433/100000000000000 : ℝ)^405
        have hw : |(1293736403/2500000000 : ℝ)|=(1293736403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5368690381/10000000000 : ℝ)*x 0 + (1034989179/2000000000 : ℝ)*x 1 + (-278646481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368690381/10000000000 : ℝ)^533 ≤ (11026392010787/25000000000000 : ℝ)^405 := by
    have hnat : (5368690381 : ℕ)^533*25000000000000^405 ≤ 11026392010787^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368690381 10000000000 11026392010787 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034989179/2000000000 : ℝ)^533 ≤ (4202289058783/10000000000000 : ℝ)^405 := by
    have hnat : (1034989179 : ℕ)^533*10000000000000^405 ≤ 4202289058783^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034989179 2000000000 4202289058783 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278646481/1250000000 : ℝ)^533 ≤ (6935770678533/50000000000000 : ℝ)^405 := by
    have hnat : (278646481 : ℕ)^533*50000000000000^405 ≤ 6935770678533^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278646481 1250000000 6935770678533 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368690381/10000000000 : ℝ), (1034989179/2000000000 : ℝ), (-278646481/1250000000 : ℝ)] ![(11026392010787/25000000000000 : ℝ), (4202289058783/10000000000000 : ℝ), (6935770678533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368690381/10000000000 : ℝ)|^533 ≤ (11026392010787/25000000000000 : ℝ)^405
        have hw : |(5368690381/10000000000 : ℝ)|=(5368690381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034989179/2000000000 : ℝ)|^533 ≤ (4202289058783/10000000000000 : ℝ)^405
        have hw : |(1034989179/2000000000 : ℝ)|=(1034989179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278646481/1250000000 : ℝ)|^533 ≤ (6935770678533/50000000000000 : ℝ)^405
        have hw : |(-278646481/1250000000 : ℝ)|=(278646481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4329368393/10000000000 : ℝ)*x 0 + (2007557191/5000000000 : ℝ)*x 1 + (1166717287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329368393/10000000000 : ℝ)^533 ≤ (16614479780469/50000000000000 : ℝ)^405 := by
    have hnat : (4329368393 : ℕ)^533*50000000000000^405 ≤ 16614479780469^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329368393 10000000000 16614479780469 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007557191/5000000000 : ℝ)^533 ≤ (30091711869267/100000000000000 : ℝ)^405 := by
    have hnat : (2007557191 : ℕ)^533*100000000000000^405 ≤ 30091711869267^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007557191 5000000000 30091711869267 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166717287/2500000000 : ℝ)^533 ≤ (36679328549411/100000000000000 : ℝ)^405 := by
    have hnat : (1166717287 : ℕ)^533*100000000000000^405 ≤ 36679328549411^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166717287 2500000000 36679328549411 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329368393/10000000000 : ℝ), (2007557191/5000000000 : ℝ), (1166717287/2500000000 : ℝ)] ![(16614479780469/50000000000000 : ℝ), (30091711869267/100000000000000 : ℝ), (36679328549411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329368393/10000000000 : ℝ)|^533 ≤ (16614479780469/50000000000000 : ℝ)^405
        have hw : |(4329368393/10000000000 : ℝ)|=(4329368393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007557191/5000000000 : ℝ)|^533 ≤ (30091711869267/100000000000000 : ℝ)^405
        have hw : |(2007557191/5000000000 : ℝ)|=(2007557191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1166717287/2500000000 : ℝ)|^533 ≤ (36679328549411/100000000000000 : ℝ)^405
        have hw : |(1166717287/2500000000 : ℝ)|=(1166717287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-516446131/2500000000 : ℝ)*x 0 + (5177012113/10000000000 : ℝ)*x 1 + (1097705503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516446131/2500000000 : ℝ)^533 ≤ (12549258425221/100000000000000 : ℝ)^405 := by
    have hnat : (516446131 : ℕ)^533*100000000000000^405 ≤ 12549258425221^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516446131 2500000000 12549258425221 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177012113/10000000000 : ℝ)^533 ≤ (21022486737001/50000000000000 : ℝ)^405 := by
    have hnat : (5177012113 : ℕ)^533*50000000000000^405 ≤ 21022486737001^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177012113 10000000000 21022486737001 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097705503/2000000000 : ℝ)^533 ≤ (11351442021619/25000000000000 : ℝ)^405 := by
    have hnat : (1097705503 : ℕ)^533*25000000000000^405 ≤ 11351442021619^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097705503 2000000000 11351442021619 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516446131/2500000000 : ℝ), (5177012113/10000000000 : ℝ), (1097705503/2000000000 : ℝ)] ![(12549258425221/100000000000000 : ℝ), (21022486737001/50000000000000 : ℝ), (11351442021619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516446131/2500000000 : ℝ)|^533 ≤ (12549258425221/100000000000000 : ℝ)^405
        have hw : |(-516446131/2500000000 : ℝ)|=(516446131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177012113/10000000000 : ℝ)|^533 ≤ (21022486737001/50000000000000 : ℝ)^405
        have hw : |(5177012113/10000000000 : ℝ)|=(5177012113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097705503/2000000000 : ℝ)|^533 ≤ (11351442021619/25000000000000 : ℝ)^405
        have hw : |(1097705503/2000000000 : ℝ)|=(1097705503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5287672279/10000000000 : ℝ)*x 0 + (-957794663/5000000000 : ℝ)*x 1 + (686065953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287672279/10000000000 : ℝ)^533 ≤ (10807928546861/25000000000000 : ℝ)^405 := by
    have hnat : (5287672279 : ℕ)^533*25000000000000^405 ≤ 10807928546861^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287672279 10000000000 10807928546861 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957794663/5000000000 : ℝ)^533 ≤ (710157282437/6250000000000 : ℝ)^405 := by
    have hnat : (957794663 : ℕ)^533*6250000000000^405 ≤ 710157282437^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957794663 5000000000 710157282437 6250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686065953/1250000000 : ℝ)^533 ≤ (45405769273211/100000000000000 : ℝ)^405 := by
    have hnat : (686065953 : ℕ)^533*100000000000000^405 ≤ 45405769273211^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686065953 1250000000 45405769273211 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287672279/10000000000 : ℝ), (-957794663/5000000000 : ℝ), (686065953/1250000000 : ℝ)] ![(10807928546861/25000000000000 : ℝ), (710157282437/6250000000000 : ℝ), (45405769273211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287672279/10000000000 : ℝ)|^533 ≤ (10807928546861/25000000000000 : ℝ)^405
        have hw : |(5287672279/10000000000 : ℝ)|=(5287672279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-957794663/5000000000 : ℝ)|^533 ≤ (710157282437/6250000000000 : ℝ)^405
        have hw : |(-957794663/5000000000 : ℝ)|=(957794663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686065953/1250000000 : ℝ)|^533 ≤ (45405769273211/100000000000000 : ℝ)^405
        have hw : |(686065953/1250000000 : ℝ)|=(686065953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5287672417/10000000000 : ℝ)*x 0 + (2744263761/5000000000 : ℝ)*x 1 + (-1915589279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287672417/10000000000 : ℝ)^533 ≤ (10807928918079/25000000000000 : ℝ)^405 := by
    have hnat : (5287672417 : ℕ)^533*25000000000000^405 ≤ 10807928918079^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287672417 10000000000 10807928918079 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744263761/5000000000 : ℝ)^533 ≤ (354732563771/781250000000 : ℝ)^405 := by
    have hnat : (2744263761 : ℕ)^533*781250000000^405 ≤ 354732563771^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744263761 5000000000 354732563771 781250000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915589279/10000000000 : ℝ)^533 ≤ (11362516152097/100000000000000 : ℝ)^405 := by
    have hnat : (1915589279 : ℕ)^533*100000000000000^405 ≤ 11362516152097^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915589279 10000000000 11362516152097 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287672417/10000000000 : ℝ), (2744263761/5000000000 : ℝ), (-1915589279/10000000000 : ℝ)] ![(10807928918079/25000000000000 : ℝ), (354732563771/781250000000 : ℝ), (11362516152097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287672417/10000000000 : ℝ)|^533 ≤ (10807928918079/25000000000000 : ℝ)^405
        have hw : |(5287672417/10000000000 : ℝ)|=(5287672417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744263761/5000000000 : ℝ)|^533 ≤ (354732563771/781250000000 : ℝ)^405
        have hw : |(2744263761/5000000000 : ℝ)|=(2744263761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915589279/10000000000 : ℝ)|^533 ≤ (11362516152097/100000000000000 : ℝ)^405
        have hw : |(-1915589279/10000000000 : ℝ)|=(1915589279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s2_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (865905651/2000000000 : ℝ)*x 0 + (58282513/125000000 : ℝ)*x 1 + (502428151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865905651/2000000000 : ℝ)^533 ≤ (33230574336481/100000000000000 : ℝ)^405 := by
    have hnat : (865905651 : ℕ)^533*100000000000000^405 ≤ 33230574336481^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865905651 2000000000 33230574336481 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58282513/125000000 : ℝ)^533 ≤ (36635187713223/100000000000000 : ℝ)^405 := by
    have hnat : (58282513 : ℕ)^533*100000000000000^405 ≤ 36635187713223^405*125000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58282513 125000000 36635187713223 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502428151/1250000000 : ℝ)^533 ≤ (15067118972669/50000000000000 : ℝ)^405 := by
    have hnat : (502428151 : ℕ)^533*50000000000000^405 ≤ 15067118972669^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502428151 1250000000 15067118972669 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865905651/2000000000 : ℝ), (58282513/125000000 : ℝ), (502428151/1250000000 : ℝ)] ![(33230574336481/100000000000000 : ℝ), (36635187713223/100000000000000 : ℝ), (15067118972669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865905651/2000000000 : ℝ)|^533 ≤ (33230574336481/100000000000000 : ℝ)^405
        have hw : |(865905651/2000000000 : ℝ)|=(865905651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58282513/125000000 : ℝ)|^533 ≤ (36635187713223/100000000000000 : ℝ)^405
        have hw : |(58282513/125000000 : ℝ)|=(58282513/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502428151/1250000000 : ℝ)|^533 ≤ (15067118972669/50000000000000 : ℝ)^405
        have hw : |(502428151/1250000000 : ℝ)|=(502428151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9877/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1199/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16263/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9877/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9877/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6527/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9877/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9877/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6527/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9877/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9877/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6527/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6527/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (1162922863791449/100000000000000000000 : ℝ) := by
    have hpowers : (6527/100000 : ℝ)^4263 ≤ (1162922863791449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6527 : ℕ)^4263*100000000000000000000^1024 ≤ 1162922863791449^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6527 100000 1162922863791449 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6527/100000 : ℝ)) (X := (1162922863791449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9877/50000 : ℝ) ^ (4263/1024 : ℝ) ≤ (116883024537272567/100000000000000000000 : ℝ) := by
    have hpowers : (9877/50000 : ℝ)^4263 ≤ (116883024537272567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9877 : ℕ)^4263*100000000000000000000^1024 ≤ 116883024537272567^1024*50000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9877 50000 116883024537272567 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9877/50000 : ℝ)) (X := (116883024537272567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001162922863791449/50000000000000000000 : ℝ) ≤ (1250006983476957/1250000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50001162922863791449/50000000000000000000 : ℝ)^1024 ≤ (1250006983476957/1250000000000000 : ℝ)^4263 := by
      have hnat : (50001162922863791449 : ℕ)^1024*1250000000000000^4263 ≤ 1250006983476957^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001162922863791449 50000000000000000000 1250006983476957 1250000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250006983476957/1250000000000000 : ℝ)) (X := (50001162922863791449/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6257377871712566501/6250000000000000000 : ℝ) ≤ (10002834268803693/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (6257377871712566501/6250000000000000000 : ℝ)^1024 ≤ (10002834268803693/10000000000000000 : ℝ)^4263 := by
      have hnat : (6257377871712566501 : ℕ)^1024*10000000000000000^4263 ≤ 10002834268803693^4263*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257377871712566501 6250000000000000000 10002834268803693 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002834268803693/10000000000000000 : ℝ)) (X := (6257377871712566501/6250000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50116883024537272567/50000000000000000000 : ℝ) ≤ (1000561266979173/1000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50116883024537272567/50000000000000000000 : ℝ)^1024 ≤ (1000561266979173/1000000000000000 : ℝ)^4263 := by
      have hnat : (50116883024537272567 : ℕ)^1024*1000000000000000^4263 ≤ 1000561266979173^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50116883024537272567 50000000000000000000 1000561266979173 1000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000561266979173/1000000000000000 : ℝ)) (X := (50116883024537272567/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1162922863791449/100000000000000000000 : ℝ) ≤ ((22039078286183307819/22045000000000000000 : ℝ)+2*(926133662679/440900000000000 : ℝ)*(6527/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (22039078286183307819/22045000000000000000 : ℝ)+2*(926133662679/440900000000000 : ℝ)*(6527/100000 : ℝ)=(1250006983476957/1250000000000000 : ℝ) by norm_num, show 1+2*(1162922863791449/100000000000000000000 : ℝ)=(50001162922863791449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(116883024537272567/100000000000000000000 : ℝ)+(1162922863791449/100000000000000000000 : ℝ) ≤ ((22039078286183307819/22045000000000000000 : ℝ)+(926133662679/440900000000000 : ℝ)*((9877/50000 : ℝ)+(6527/100000 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (22039078286183307819/22045000000000000000 : ℝ)+(926133662679/440900000000000 : ℝ)*((9877/50000 : ℝ)+(6527/100000 : ℝ))=(10002834268803693/10000000000000000 : ℝ) by norm_num, show 1+(116883024537272567/100000000000000000000 : ℝ)+(1162922863791449/100000000000000000000 : ℝ)=(6257377871712566501/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(116883024537272567/100000000000000000000 : ℝ) ≤ ((22039078286183307819/22045000000000000000 : ℝ)+2*(926133662679/440900000000000 : ℝ)*(9877/50000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (22039078286183307819/22045000000000000000 : ℝ)+2*(926133662679/440900000000000 : ℝ)*(9877/50000 : ℝ)=(1000561266979173/1000000000000000 : ℝ) by norm_num, show 1+2*(116883024537272567/100000000000000000000 : ℝ)=(50116883024537272567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22039078286183307819/22045000000000000000 : ℝ)*(X 1 0+X 2 0)+(926133662679/440900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (6527/100000 : ℝ)) (hi := (9877/50000 : ℝ)) (c := (22039078286183307819/22045000000000000000 : ℝ)) (alpha := (926133662679/440900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22039078286183307819/22045000000000000000 : ℝ)*(X 0 1+X 2 1)+(926133662679/440900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (6527/100000 : ℝ)) (hi := (9877/50000 : ℝ)) (c := (22039078286183307819/22045000000000000000 : ℝ)) (alpha := (926133662679/440900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22039078286183307819/22045000000000000000 : ℝ)*(X 0 2+X 1 2)+(926133662679/440900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (6527/100000 : ℝ)) (hi := (9877/50000 : ℝ)) (c := (22039078286183307819/22045000000000000000 : ℝ)) (alpha := (926133662679/440900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2065706641/10000000000 : ℝ)*X 0 0+(1098122583/2000000000 : ℝ)*X 0 1+(5174945841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((536869073/1000000000 : ℝ)*X 1 0+(-557292939/2500000000 : ℝ)*X 1 1+(1293736403/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368690381/10000000000 : ℝ)*X 2 0+(1034989179/2000000000 : ℝ)*X 2 1+(-278646481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329368393/10000000000 : ℝ)*X 0 0+(2007557191/5000000000 : ℝ)*X 0 1+(1166717287/2500000000 : ℝ)*X 0 2+(4329368393/10000000000 : ℝ)*X 1 0+(2007557191/5000000000 : ℝ)*X 1 1+(1166717287/2500000000 : ℝ)*X 1 2+(4329368393/10000000000 : ℝ)*X 2 0+(2007557191/5000000000 : ℝ)*X 2 1+(1166717287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-516446131/2500000000 : ℝ)*X 0 0+(5177012113/10000000000 : ℝ)*X 0 1+(1097705503/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287672279/10000000000 : ℝ)*X 1 0+(-957794663/5000000000 : ℝ)*X 1 1+(686065953/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287672417/10000000000 : ℝ)*X 2 0+(2744263761/5000000000 : ℝ)*X 2 1+(-1915589279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865905651/2000000000 : ℝ)*X 0 0+(58282513/125000000 : ℝ)*X 0 1+(502428151/1250000000 : ℝ)*X 0 2+(865905651/2000000000 : ℝ)*X 1 0+(58282513/125000000 : ℝ)*X 1 1+(502428151/1250000000 : ℝ)*X 1 2+(865905651/2000000000 : ℝ)*X 2 0+(58282513/125000000 : ℝ)*X 2 1+(502428151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1590624137949121780209872163/1102250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1250526909/100000000000000 : ℝ)*(base19) + (693020369/100000000000000 : ℝ)*(base23) + (7549931/4000000000000 : ℝ)*(lower2) + (32999109/6250000000000 : ℝ)*(upper3) + (128649687/100000000000000 : ℝ)*(upper5) + (2351121728232447/100000000000000 : ℝ)*(major0) + (2351121728232447/100000000000000 : ℝ)*(major1) + (2351121728232447/100000000000000 : ℝ)*(major2) + (791975399564839/25000000000000 : ℝ)*(sp0) + (39598755484853/1250000000000 : ℝ)*(sp1) + (158395049814739/5000000000000 : ℝ)*(sp2) + (767164300408623/50000000000000 : ℝ)*(sp3) + (91055793/100000000000000 : ℝ)*(sp4) + (262364603/2000000000000 : ℝ)*(sp7) + (1534341719047397/100000000000000 : ℝ)*(f.failure) + (3167901689315149/100000000000000 : ℝ)*(f.sum) + (92970357501513/22045000000000000000000000000 : ℝ)*base65 + (24334986062715753093/2204500000000000000000000000000000 : ℝ)*base67 + (11226502015264753093/2204500000000000000000000000000000 : ℝ)*base69 + (5960218857184253093/2204500000000000000000000000000000 : ℝ)*base71 + (199787744307573/22045000000000000000000000000 : ℝ)*base73 + (22837559229064253093/2204500000000000000000000000000000 : ℝ)*base75 + (15868352969274253093/2204500000000000000000000000000000 : ℝ)*base77 + (30776700949136253093/2204500000000000000000000000000000 : ℝ)*base79 + (65988799311953/22045000000000000000000000000 : ℝ)*base81 + (3492441/10000000000000000000000 : ℝ)*base89 + (3492441/10000000000000000000000 : ℝ)*base91 + (3492441/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1236499698852692125673397003/275562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (887208131/100000000000000 : ℝ)*(base19) + (576902123/50000000000000 : ℝ)*(base23) + (1190153/800000000000 : ℝ)*(upper3) + (65683133/100000000000000 : ℝ)*(lower4) + (18022497/50000000000000 : ℝ)*(upper5) + (1191224356620279/50000000000000 : ℝ)*(major0) + (1191224356620279/50000000000000 : ℝ)*(major1) + (1191224356620279/50000000000000 : ℝ)*(major2) + (913581067/10000000000000 : ℝ)*(sp1) + (1296028047/10000000000000 : ℝ)*(sp2) + (3210111571719/100000000000 : ℝ)*(sp4) + (1605050774350099/50000000000000 : ℝ)*(sp5) + (802524364408571/25000000000000 : ℝ)*(sp6) + (1554785705189303/100000000000000 : ℝ)*(sp7) + (1554785705189303/100000000000000 : ℝ)*(f.failure) + (3210111571719/100000000000 : ℝ)*(f.sum) + (18059400392957/22045000000000000000000000000 : ℝ)*base65 + (9058968777843288499/1102250000000000000000000000000000 : ℝ)*base68 + (7656921001277288499/1102250000000000000000000000000000 : ℝ)*base70 + (7626963591139038499/1102250000000000000000000000000000 : ℝ)*base72 + (37141918625729/11022500000000000000000000000 : ℝ)*base74 + (3973729352190711501/1102250000000000000000000000000000 : ℝ)*base75 + (375264319840038499/1102250000000000000000000000000000 : ℝ)*base78 + (11029447763413788499/1102250000000000000000000000000000 : ℝ)*base80 + (20325421395689/11022500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (79492659/10000000000000000000000 : ℝ)*base89 + (79492659/10000000000000000000000 : ℝ)*base91 + (79492659/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1304_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9877/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6527/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1304_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1304_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1304_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1304_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1304_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
