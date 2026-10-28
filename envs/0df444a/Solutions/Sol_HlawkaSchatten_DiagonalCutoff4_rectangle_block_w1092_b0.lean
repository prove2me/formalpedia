-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1092_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:14.067141+00:00
-- url     : https://prove2.me/submissions/4fc64ad9-8880-43a0-a586-3d9d82cc15f9

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
theorem support_rectangle_w1092_s0_0 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-953868503/5000000000 : ℝ)*x 0 + (6065958899/10000000000 : ℝ)*x 1 + (190964649/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953868503/5000000000 : ℝ)^8285 ≤ (5536526840371/50000000000000 : ℝ)^6237 := by
    have hnat : (953868503 : ℕ)^8285*50000000000000^6237 ≤ 5536526840371^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953868503 5000000000 5536526840371 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6065958899/10000000000 : ℝ)^8285 ≤ (51476816509259/100000000000000 : ℝ)^6237 := by
    have hnat : (6065958899 : ℕ)^8285*100000000000000^6237 ≤ 51476816509259^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6065958899 10000000000 51476816509259 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190964649/400000000 : ℝ)^8285 ≤ (3745012980281/10000000000000 : ℝ)^6237 := by
    have hnat : (190964649 : ℕ)^8285*10000000000000^6237 ≤ 3745012980281^6237*400000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190964649 400000000 3745012980281 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953868503/5000000000 : ℝ), (6065958899/10000000000 : ℝ), (190964649/400000000 : ℝ)] ![(5536526840371/50000000000000 : ℝ), (51476816509259/100000000000000 : ℝ), (3745012980281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953868503/5000000000 : ℝ)|^8285 ≤ (5536526840371/50000000000000 : ℝ)^6237
        have hw : |(-953868503/5000000000 : ℝ)|=(953868503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6065958899/10000000000 : ℝ)|^8285 ≤ (51476816509259/100000000000000 : ℝ)^6237
        have hw : |(6065958899/10000000000 : ℝ)|=(6065958899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190964649/400000000 : ℝ)|^8285 ≤ (3745012980281/10000000000000 : ℝ)^6237
        have hw : |(190964649/400000000 : ℝ)|=(190964649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_1 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5519609619/10000000000 : ℝ)*x 0 + (-2650561427/10000000000 : ℝ)*x 1 + (190964649/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519609619/10000000000 : ℝ)^8285 ≤ (9082190677071/20000000000000 : ℝ)^6237 := by
    have hnat : (5519609619 : ℕ)^8285*20000000000000^6237 ≤ 9082190677071^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519609619 10000000000 9082190677071 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2650561427/10000000000 : ℝ)^8285 ≤ (4284729199881/25000000000000 : ℝ)^6237 := by
    have hnat : (2650561427 : ℕ)^8285*25000000000000^6237 ≤ 4284729199881^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650561427 10000000000 4284729199881 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190964649/400000000 : ℝ)^8285 ≤ (3745012980281/10000000000000 : ℝ)^6237 := by
    have hnat : (190964649 : ℕ)^8285*10000000000000^6237 ≤ 3745012980281^6237*400000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190964649 400000000 3745012980281 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519609619/10000000000 : ℝ), (-2650561427/10000000000 : ℝ), (190964649/400000000 : ℝ)] ![(9082190677071/20000000000000 : ℝ), (4284729199881/25000000000000 : ℝ), (3745012980281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519609619/10000000000 : ℝ)|^8285 ≤ (9082190677071/20000000000000 : ℝ)^6237
        have hw : |(5519609619/10000000000 : ℝ)|=(5519609619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2650561427/10000000000 : ℝ)|^8285 ≤ (4284729199881/25000000000000 : ℝ)^6237
        have hw : |(-2650561427/10000000000 : ℝ)|=(2650561427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190964649/400000000 : ℝ)|^8285 ≤ (3745012980281/10000000000000 : ℝ)^6237
        have hw : |(190964649/400000000 : ℝ)|=(190964649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_2 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5519609619/10000000000 : ℝ)*x 0 + (190964649/400000000 : ℝ)*x 1 + (-2650561427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519609619/10000000000 : ℝ)^8285 ≤ (9082190677071/20000000000000 : ℝ)^6237 := by
    have hnat : (5519609619 : ℕ)^8285*20000000000000^6237 ≤ 9082190677071^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519609619 10000000000 9082190677071 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190964649/400000000 : ℝ)^8285 ≤ (3745012980281/10000000000000 : ℝ)^6237 := by
    have hnat : (190964649 : ℕ)^8285*10000000000000^6237 ≤ 3745012980281^6237*400000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190964649 400000000 3745012980281 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2650561427/10000000000 : ℝ)^8285 ≤ (4284729199881/25000000000000 : ℝ)^6237 := by
    have hnat : (2650561427 : ℕ)^8285*25000000000000^6237 ≤ 4284729199881^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650561427 10000000000 4284729199881 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519609619/10000000000 : ℝ), (190964649/400000000 : ℝ), (-2650561427/10000000000 : ℝ)] ![(9082190677071/20000000000000 : ℝ), (3745012980281/10000000000000 : ℝ), (4284729199881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519609619/10000000000 : ℝ)|^8285 ≤ (9082190677071/20000000000000 : ℝ)^6237
        have hw : |(5519609619/10000000000 : ℝ)|=(5519609619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(190964649/400000000 : ℝ)|^8285 ≤ (3745012980281/10000000000000 : ℝ)^6237
        have hw : |(190964649/400000000 : ℝ)|=(190964649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2650561427/10000000000 : ℝ)|^8285 ≤ (4284729199881/25000000000000 : ℝ)^6237
        have hw : |(-2650561427/10000000000 : ℝ)|=(2650561427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_3 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4205065607/10000000000 : ℝ)*x 0 + (3123509663/10000000000 : ℝ)*x 1 + (5668416167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205065607/10000000000 : ℝ)^8285 ≤ (6327959247119/20000000000000 : ℝ)^6237 := by
    have hnat : (4205065607 : ℕ)^8285*20000000000000^6237 ≤ 6327959247119^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205065607 10000000000 6327959247119 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123509663/10000000000 : ℝ)^8285 ≤ (5328957742967/25000000000000 : ℝ)^6237 := by
    have hnat : (3123509663 : ℕ)^8285*25000000000000^6237 ≤ 5328957742967^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123509663 10000000000 5328957742967 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5668416167/10000000000 : ℝ)^8285 ≤ (5880546597261/12500000000000 : ℝ)^6237 := by
    have hnat : (5668416167 : ℕ)^8285*12500000000000^6237 ≤ 5880546597261^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5668416167 10000000000 5880546597261 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205065607/10000000000 : ℝ), (3123509663/10000000000 : ℝ), (5668416167/10000000000 : ℝ)] ![(6327959247119/20000000000000 : ℝ), (5328957742967/25000000000000 : ℝ), (5880546597261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205065607/10000000000 : ℝ)|^8285 ≤ (6327959247119/20000000000000 : ℝ)^6237
        have hw : |(4205065607/10000000000 : ℝ)|=(4205065607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123509663/10000000000 : ℝ)|^8285 ≤ (5328957742967/25000000000000 : ℝ)^6237
        have hw : |(3123509663/10000000000 : ℝ)|=(3123509663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5668416167/10000000000 : ℝ)|^8285 ≤ (5880546597261/12500000000000 : ℝ)^6237
        have hw : |(5668416167/10000000000 : ℝ)|=(5668416167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_4 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-239129017/1250000000 : ℝ)*x 0 + (300466481/625000000 : ℝ)*x 1 + (1206288479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239129017/1250000000 : ℝ)^8285 ≤ (1389237348471/12500000000000 : ℝ)^6237 := by
    have hnat : (239129017 : ℕ)^8285*12500000000000^6237 ≤ 1389237348471^6237*1250000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239129017 1250000000 1389237348471 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300466481/625000000 : ℝ)^8285 ≤ (37798015847193/100000000000000 : ℝ)^6237 := by
    have hnat : (300466481 : ℕ)^8285*100000000000000^6237 ≤ 37798015847193^6237*625000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300466481 625000000 37798015847193 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206288479/2000000000 : ℝ)^8285 ≤ (51088085352191/100000000000000 : ℝ)^6237 := by
    have hnat : (1206288479 : ℕ)^8285*100000000000000^6237 ≤ 51088085352191^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206288479 2000000000 51088085352191 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239129017/1250000000 : ℝ), (300466481/625000000 : ℝ), (1206288479/2000000000 : ℝ)] ![(1389237348471/12500000000000 : ℝ), (37798015847193/100000000000000 : ℝ), (51088085352191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239129017/1250000000 : ℝ)|^8285 ≤ (1389237348471/12500000000000 : ℝ)^6237
        have hw : |(-239129017/1250000000 : ℝ)|=(239129017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300466481/625000000 : ℝ)|^8285 ≤ (37798015847193/100000000000000 : ℝ)^6237
        have hw : |(300466481/625000000 : ℝ)|=(300466481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206288479/2000000000 : ℝ)|^8285 ≤ (51088085352191/100000000000000 : ℝ)^6237
        have hw : |(1206288479/2000000000 : ℝ)|=(1206288479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_5 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168842913/10000000000 : ℝ)*x 0 + (-27864749/200000000 : ℝ)*x 1 + (188482561/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168842913/10000000000 : ℝ)^8285 ≤ (10404526459573/25000000000000 : ℝ)^6237 := by
    have hnat : (5168842913 : ℕ)^8285*25000000000000^6237 ≤ 10404526459573^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168842913 10000000000 10404526459573 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27864749/200000000 : ℝ)^8285 ≤ (3646906888867/50000000000000 : ℝ)^6237 := by
    have hnat : (27864749 : ℕ)^8285*50000000000000^6237 ≤ 3646906888867^6237*200000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27864749 200000000 3646906888867 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188482561/312500000 : ℝ)^8285 ≤ (25544040183861/50000000000000 : ℝ)^6237 := by
    have hnat : (188482561 : ℕ)^8285*50000000000000^6237 ≤ 25544040183861^6237*312500000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188482561 312500000 25544040183861 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168842913/10000000000 : ℝ), (-27864749/200000000 : ℝ), (188482561/312500000 : ℝ)] ![(10404526459573/25000000000000 : ℝ), (3646906888867/50000000000000 : ℝ), (25544040183861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168842913/10000000000 : ℝ)|^8285 ≤ (10404526459573/25000000000000 : ℝ)^6237
        have hw : |(5168842913/10000000000 : ℝ)|=(5168842913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27864749/200000000 : ℝ)|^8285 ≤ (3646906888867/50000000000000 : ℝ)^6237
        have hw : |(-27864749/200000000 : ℝ)|=(27864749/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188482561/312500000 : ℝ)|^8285 ≤ (25544040183861/50000000000000 : ℝ)^6237
        have hw : |(188482561/312500000 : ℝ)|=(188482561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_6 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5168843547/10000000000 : ℝ)*x 0 + (3015721293/5000000000 : ℝ)*x 1 + (-27864709/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168843547/10000000000 : ℝ)^8285 ≤ (2601132038707/6250000000000 : ℝ)^6237 := by
    have hnat : (5168843547 : ℕ)^8285*6250000000000^6237 ≤ 2601132038707^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168843547 10000000000 2601132038707 6250000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015721293/5000000000 : ℝ)^8285 ≤ (51088087501251/100000000000000 : ℝ)^6237 := by
    have hnat : (3015721293 : ℕ)^8285*100000000000000^6237 ≤ 51088087501251^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015721293 5000000000 51088087501251 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27864709/200000000 : ℝ)^8285 ≤ (1458759973873/20000000000000 : ℝ)^6237 := by
    have hnat : (27864709 : ℕ)^8285*20000000000000^6237 ≤ 1458759973873^6237*200000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27864709 200000000 1458759973873 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168843547/10000000000 : ℝ), (3015721293/5000000000 : ℝ), (-27864709/200000000 : ℝ)] ![(2601132038707/6250000000000 : ℝ), (51088087501251/100000000000000 : ℝ), (1458759973873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168843547/10000000000 : ℝ)|^8285 ≤ (2601132038707/6250000000000 : ℝ)^6237
        have hw : |(5168843547/10000000000 : ℝ)|=(5168843547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015721293/5000000000 : ℝ)|^8285 ≤ (51088087501251/100000000000000 : ℝ)^6237
        have hw : |(3015721293/5000000000 : ℝ)|=(3015721293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27864709/200000000 : ℝ)|^8285 ≤ (1458759973873/20000000000000 : ℝ)^6237
        have hw : |(-27864709/200000000 : ℝ)|=(27864709/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s0_7 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4215494219/10000000000 : ℝ)*x 0 + (1400680437/2500000000 : ℝ)*x 1 + (638301343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215494219/10000000000 : ℝ)^8285 ≤ (992002231217/3125000000000 : ℝ)^6237 := by
    have hnat : (4215494219 : ℕ)^8285*3125000000000^6237 ≤ 992002231217^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215494219 10000000000 992002231217 3125000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400680437/2500000000 : ℝ)^8285 ≤ (1447546874391/3125000000000 : ℝ)^6237 := by
    have hnat : (1400680437 : ℕ)^8285*3125000000000^6237 ≤ 1447546874391^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400680437 2500000000 1447546874391 3125000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638301343/2000000000 : ℝ)^8285 ≤ (21934428610781/100000000000000 : ℝ)^6237 := by
    have hnat : (638301343 : ℕ)^8285*100000000000000^6237 ≤ 21934428610781^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638301343 2000000000 21934428610781 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215494219/10000000000 : ℝ), (1400680437/2500000000 : ℝ), (638301343/2000000000 : ℝ)] ![(992002231217/3125000000000 : ℝ), (1447546874391/3125000000000 : ℝ), (21934428610781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215494219/10000000000 : ℝ)|^8285 ≤ (992002231217/3125000000000 : ℝ)^6237
        have hw : |(4215494219/10000000000 : ℝ)|=(4215494219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400680437/2500000000 : ℝ)|^8285 ≤ (1447546874391/3125000000000 : ℝ)^6237
        have hw : |(1400680437/2500000000 : ℝ)|=(1400680437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638301343/2000000000 : ℝ)|^8285 ≤ (21934428610781/100000000000000 : ℝ)^6237
        have hw : |(638301343/2000000000 : ℝ)|=(638301343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1092_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (103/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3501/12500 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (2071/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2071 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2071*1^512 ≤ 0^512*1^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2071/512 : ℝ) ≤ (614191444638127723/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2071 ≤ (614191444638127723/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2071*25000000000000000000^512 ≤ 614191444638127723^512*5^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 614191444638127723 25000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (614191444638127723/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2071 := by
      have hnat : (1 : ℕ)^512*1^2071 ≤ 1^2071*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25614191444638127723/25000000000000000000 : ℝ) ≤ (10060183332832053/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25614191444638127723/25000000000000000000 : ℝ)^512 ≤ (10060183332832053/10000000000000000 : ℝ)^2071 := by
      have hnat : (25614191444638127723 : ℕ)^512*10000000000000000^2071 ≤ 10060183332832053^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25614191444638127723 25000000000000000000 10060183332832053 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060183332832053/10000000000000000 : ℝ)) (X := (25614191444638127723/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13114191444638127723/12500000000000000000 : ℝ) ≤ (5060183332832053/5000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (13114191444638127723/12500000000000000000 : ℝ)^512 ≤ (5060183332832053/5000000000000000 : ℝ)^2071 := by
      have hnat : (13114191444638127723 : ℕ)^512*5000000000000000^2071 ≤ 5060183332832053^2071*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13114191444638127723 12500000000000000000 5060183332832053 5000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5060183332832053/5000000000000000 : ℝ)) (X := (13114191444638127723/12500000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(60183332832053/4000000000000000 : ℝ)*(0 : ℝ))^(2071/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(60183332832053/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(614191444638127723/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(60183332832053/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2071/512 : ℝ) := by
    rw [show (1 : ℝ)+(60183332832053/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10060183332832053/10000000000000000 : ℝ) by norm_num, show 1+(614191444638127723/25000000000000000000 : ℝ)+(0 : ℝ)=(25614191444638127723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(614191444638127723/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(60183332832053/4000000000000000 : ℝ)*(2/5 : ℝ))^(2071/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(60183332832053/4000000000000000 : ℝ)*(2/5 : ℝ)=(5060183332832053/5000000000000000 : ℝ) by norm_num, show 1+2*(614191444638127723/25000000000000000000 : ℝ)=(13114191444638127723/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(60183332832053/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60183332832053/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(60183332832053/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60183332832053/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(60183332832053/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (60183332832053/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-953868503/5000000000 : ℝ)*X 0 0+(6065958899/10000000000 : ℝ)*X 0 1+(190964649/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5519609619/10000000000 : ℝ)*X 1 0+(-2650561427/10000000000 : ℝ)*X 1 1+(190964649/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5519609619/10000000000 : ℝ)*X 2 0+(190964649/400000000 : ℝ)*X 2 1+(-2650561427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205065607/10000000000 : ℝ)*X 0 0+(3123509663/10000000000 : ℝ)*X 0 1+(5668416167/10000000000 : ℝ)*X 0 2+(4205065607/10000000000 : ℝ)*X 1 0+(3123509663/10000000000 : ℝ)*X 1 1+(5668416167/10000000000 : ℝ)*X 1 2+(4205065607/10000000000 : ℝ)*X 2 0+(3123509663/10000000000 : ℝ)*X 2 1+(5668416167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-239129017/1250000000 : ℝ)*X 0 0+(300466481/625000000 : ℝ)*X 0 1+(1206288479/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168842913/10000000000 : ℝ)*X 1 0+(-27864749/200000000 : ℝ)*X 1 1+(188482561/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168843547/10000000000 : ℝ)*X 2 0+(3015721293/5000000000 : ℝ)*X 2 1+(-27864709/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215494219/10000000000 : ℝ)*X 0 0+(1400680437/2500000000 : ℝ)*X 0 1+(638301343/2000000000 : ℝ)*X 0 2+(4215494219/10000000000 : ℝ)*X 1 0+(1400680437/2500000000 : ℝ)*X 1 1+(638301343/2000000000 : ℝ)*X 1 2+(4215494219/10000000000 : ℝ)*X 2 0+(1400680437/2500000000 : ℝ)*X 2 1+(638301343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75285547551311251743747/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5026491/12500000000000 : ℝ)*(base1) + (940207969/100000000000000 : ℝ)*(base19) + (876374959/100000000000000 : ℝ)*(base23) + (6383301/10000000000000 : ℝ)*(base24) + (212776699/100000000000000 : ℝ)*(upper3) + (58351886776511/10000000000000 : ℝ)*(major0) + (58351886776511/10000000000000 : ℝ)*(major1) + (58351886776511/10000000000000 : ℝ)*(major2) + (38704558784387/5000000000000 : ℝ)*(sp0) + (774092258116943/100000000000000 : ℝ)*(sp1) + (774092258116943/100000000000000 : ℝ)*(sp2) + (78588544359127/20000000000000 : ℝ)*(sp3) + (20628491/1000000000000 : ℝ)*(sp4) + (412430457/25000000000000 : ℝ)*(sp7) + (392944411729391/100000000000000 : ℝ)*(f.failure) + (48380824895307/6250000000000 : ℝ)*(f.sum) + (42160366432917/20000000000000000000000000000 : ℝ)*base66 + (246001620052917/40000000000000000000000000000 : ℝ)*base68 + (76031425707083/40000000000000000000000000000 : ℝ)*base69 + (259157791452917/40000000000000000000000000000 : ℝ)*base72 + (41210865452917/20000000000000000000000000000 : ℝ)*base74 + (93109541292917/40000000000000000000000000000 : ℝ)*base76 + (259157791452917/40000000000000000000000000000 : ℝ)*base78 + (167970752652917/40000000000000000000000000000 : ℝ)*base80 + (116219740227083/20000000000000000000000000000 : ℝ)*base81 + (4143463/625000000000000000000 : ℝ)*base89 + (4143463/625000000000000000000 : ℝ)*base91 + (4143463/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1133623400347021107/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (892724653/100000000000000 : ℝ)*(base19) + (346750673/25000000000000 : ℝ)*(base23) + (73383517/20000000000000 : ℝ)*(base39) + (229411979/100000000000000 : ℝ)*(base45) + (88677683/100000000000000 : ℝ)*(upper3) + (318325807/100000000000000 : ℝ)*(upper5) + (153966528272329/25000000000000 : ℝ)*(major0) + (153966528272329/25000000000000 : ℝ)*(major1) + (615865746171731/100000000000000 : ℝ)*(major2) + (557442163/100000000000000 : ℝ)*(sp2) + (408502234016651/50000000000000 : ℝ)*(sp4) + (817003575308649/100000000000000 : ℝ)*(sp5) + (817002890506033/100000000000000 : ℝ)*(sp6) + (207363601145253/50000000000000 : ℝ)*(sp7) + (207363601145253/50000000000000 : ℝ)*(f.failure) + (102125604368861/12500000000000 : ℝ)*(f.sum) + (1007994360860509/400000000000000000000000000000 : ℝ)*base66 + (651835647293743/400000000000000000000000000000 : ℝ)*base67 + (750930196161437/100000000000000000000000000000 : ℝ)*base69 + (448351378893743/400000000000000000000000000000 : ℝ)*base71 + (258805439260509/400000000000000000000000000000 : ℝ)*base74 + (53689740361437/100000000000000000000000000000 : ℝ)*base75 + (2548172038563/100000000000000000000000000000 : ℝ)*base78 + (603995245938563/100000000000000000000000000000 : ℝ)*base80 + (42667237211437/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1626829/312500000000000000000 : ℝ)*base89 + (1626829/312500000000000000000 : ℝ)*base91 + (1626829/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1092_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (103/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1092_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1092_s1_0 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529001119/2500000000 : ℝ)*x 0 + (1428771943/2500000000 : ℝ)*x 1 + (2495814727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529001119/2500000000 : ℝ)^8285 ≤ (12706946072541/100000000000000 : ℝ)^6237 := by
    have hnat : (529001119 : ℕ)^8285*100000000000000^6237 ≤ 12706946072541^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529001119 2500000000 12706946072541 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1428771943/2500000000 : ℝ)^8285 ≤ (47559602690973/100000000000000 : ℝ)^6237 := by
    have hnat : (1428771943 : ℕ)^8285*100000000000000^6237 ≤ 47559602690973^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428771943 2500000000 47559602690973 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495814727/5000000000 : ℝ)^8285 ≤ (9933362805639/25000000000000 : ℝ)^6237 := by
    have hnat : (2495814727 : ℕ)^8285*25000000000000^6237 ≤ 9933362805639^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495814727 5000000000 9933362805639 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529001119/2500000000 : ℝ), (1428771943/2500000000 : ℝ), (2495814727/5000000000 : ℝ)] ![(12706946072541/100000000000000 : ℝ), (47559602690973/100000000000000 : ℝ), (9933362805639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529001119/2500000000 : ℝ)|^8285 ≤ (12706946072541/100000000000000 : ℝ)^6237
        have hw : |(-529001119/2500000000 : ℝ)|=(529001119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1428771943/2500000000 : ℝ)|^8285 ≤ (47559602690973/100000000000000 : ℝ)^6237
        have hw : |(1428771943/2500000000 : ℝ)|=(1428771943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2495814727/5000000000 : ℝ)|^8285 ≤ (9933362805639/25000000000000 : ℝ)^6237
        have hw : |(2495814727/5000000000 : ℝ)|=(2495814727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_1 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421876433/10000000000 : ℝ)*x 0 + (-2507434007/10000000000 : ℝ)*x 1 + (998325931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421876433/10000000000 : ℝ)^8285 ≤ (22172986443533/50000000000000 : ℝ)^6237 := by
    have hnat : (5421876433 : ℕ)^8285*50000000000000^6237 ≤ 22172986443533^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421876433 10000000000 22172986443533 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2507434007/10000000000 : ℝ)^8285 ≤ (3184114749221/20000000000000 : ℝ)^6237 := by
    have hnat : (2507434007 : ℕ)^8285*20000000000000^6237 ≤ 3184114749221^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507434007 10000000000 3184114749221 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998325931/2000000000 : ℝ)^8285 ≤ (2483340834243/6250000000000 : ℝ)^6237 := by
    have hnat : (998325931 : ℕ)^8285*6250000000000^6237 ≤ 2483340834243^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998325931 2000000000 2483340834243 6250000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421876433/10000000000 : ℝ), (-2507434007/10000000000 : ℝ), (998325931/2000000000 : ℝ)] ![(22172986443533/50000000000000 : ℝ), (3184114749221/20000000000000 : ℝ), (2483340834243/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421876433/10000000000 : ℝ)|^8285 ≤ (22172986443533/50000000000000 : ℝ)^6237
        have hw : |(5421876433/10000000000 : ℝ)|=(5421876433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2507434007/10000000000 : ℝ)|^8285 ≤ (3184114749221/20000000000000 : ℝ)^6237
        have hw : |(-2507434007/10000000000 : ℝ)|=(2507434007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998325931/2000000000 : ℝ)|^8285 ≤ (2483340834243/6250000000000 : ℝ)^6237
        have hw : |(998325931/2000000000 : ℝ)|=(998325931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_2 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1355469341/2500000000 : ℝ)*x 0 + (499162871/1000000000 : ℝ)*x 1 + (-2507433993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355469341/2500000000 : ℝ)^8285 ≤ (22172991501093/50000000000000 : ℝ)^6237 := by
    have hnat : (1355469341 : ℕ)^8285*50000000000000^6237 ≤ 22172991501093^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355469341 2500000000 22172991501093 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499162871/1000000000 : ℝ)^8285 ≤ (7946688671131/20000000000000 : ℝ)^6237 := by
    have hnat : (499162871 : ℕ)^8285*20000000000000^6237 ≤ 7946688671131^6237*1000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499162871 1000000000 7946688671131 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2507433993/10000000000 : ℝ)^8285 ≤ (7960286814013/50000000000000 : ℝ)^6237 := by
    have hnat : (2507433993 : ℕ)^8285*50000000000000^6237 ≤ 7960286814013^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507433993 10000000000 7960286814013 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355469341/2500000000 : ℝ), (499162871/1000000000 : ℝ), (-2507433993/10000000000 : ℝ)] ![(22172991501093/50000000000000 : ℝ), (7946688671131/20000000000000 : ℝ), (7960286814013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355469341/2500000000 : ℝ)|^8285 ≤ (22172991501093/50000000000000 : ℝ)^6237
        have hw : |(1355469341/2500000000 : ℝ)|=(1355469341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499162871/1000000000 : ℝ)|^8285 ≤ (7946688671131/20000000000000 : ℝ)^6237
        have hw : |(499162871/1000000000 : ℝ)|=(499162871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2507433993/10000000000 : ℝ)|^8285 ≤ (7960286814013/50000000000000 : ℝ)^6237
        have hw : |(-2507433993/10000000000 : ℝ)|=(2507433993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_3 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4321641873/10000000000 : ℝ)*x 0 + (3667550771/10000000000 : ℝ)*x 1 + (5092748971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321641873/10000000000 : ℝ)^8285 ≤ (32810233056061/100000000000000 : ℝ)^6237 := by
    have hnat : (4321641873 : ℕ)^8285*100000000000000^6237 ≤ 32810233056061^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321641873 10000000000 32810233056061 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3667550771/10000000000 : ℝ)^8285 ≤ (26383558898897/100000000000000 : ℝ)^6237 := by
    have hnat : (3667550771 : ℕ)^8285*100000000000000^6237 ≤ 26383558898897^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3667550771 10000000000 26383558898897 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5092748971/10000000000 : ℝ)^8285 ≤ (40806208031917/100000000000000 : ℝ)^6237 := by
    have hnat : (5092748971 : ℕ)^8285*100000000000000^6237 ≤ 40806208031917^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092748971 10000000000 40806208031917 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321641873/10000000000 : ℝ), (3667550771/10000000000 : ℝ), (5092748971/10000000000 : ℝ)] ![(32810233056061/100000000000000 : ℝ), (26383558898897/100000000000000 : ℝ), (40806208031917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321641873/10000000000 : ℝ)|^8285 ≤ (32810233056061/100000000000000 : ℝ)^6237
        have hw : |(4321641873/10000000000 : ℝ)|=(4321641873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3667550771/10000000000 : ℝ)|^8285 ≤ (26383558898897/100000000000000 : ℝ)^6237
        have hw : |(3667550771/10000000000 : ℝ)|=(3667550771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5092748971/10000000000 : ℝ)|^8285 ≤ (40806208031917/100000000000000 : ℝ)^6237
        have hw : |(5092748971/10000000000 : ℝ)|=(5092748971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_4 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058441553/5000000000 : ℝ)*x 0 + (1250424461/2500000000 : ℝ)*x 1 + (5704816753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058441553/5000000000 : ℝ)^8285 ≤ (3178488852643/25000000000000 : ℝ)^6237 := by
    have hnat : (1058441553 : ℕ)^8285*25000000000000^6237 ≤ 3178488852643^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058441553 5000000000 3178488852643 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250424461/2500000000 : ℝ)^8285 ≤ (9959986878381/25000000000000 : ℝ)^6237 := by
    have hnat : (1250424461 : ℕ)^8285*25000000000000^6237 ≤ 9959986878381^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250424461 2500000000 9959986878381 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5704816753/10000000000 : ℝ)^8285 ≤ (23723048530977/50000000000000 : ℝ)^6237 := by
    have hnat : (5704816753 : ℕ)^8285*50000000000000^6237 ≤ 23723048530977^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704816753 10000000000 23723048530977 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058441553/5000000000 : ℝ), (1250424461/2500000000 : ℝ), (5704816753/10000000000 : ℝ)] ![(3178488852643/25000000000000 : ℝ), (9959986878381/25000000000000 : ℝ), (23723048530977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058441553/5000000000 : ℝ)|^8285 ≤ (3178488852643/25000000000000 : ℝ)^6237
        have hw : |(-1058441553/5000000000 : ℝ)|=(1058441553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250424461/2500000000 : ℝ)|^8285 ≤ (9959986878381/25000000000000 : ℝ)^6237
        have hw : |(1250424461/2500000000 : ℝ)|=(1250424461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5704816753/10000000000 : ℝ)|^8285 ≤ (23723048530977/50000000000000 : ℝ)^6237
        have hw : |(5704816753/10000000000 : ℝ)|=(5704816753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_5 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309216481/2500000000 : ℝ)*x 0 + (-35884933/200000000 : ℝ)*x 1 + (2852408297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309216481/2500000000 : ℝ)^8285 ≤ (10586805281577/25000000000000 : ℝ)^6237 := by
    have hnat : (1309216481 : ℕ)^8285*25000000000000^6237 ≤ 10586805281577^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309216481 2500000000 10586805281577 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35884933/200000000 : ℝ)^8285 ≤ (1020668355439/10000000000000 : ℝ)^6237 := by
    have hnat : (35884933 : ℕ)^8285*10000000000000^6237 ≤ 1020668355439^6237*200000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35884933 200000000 1020668355439 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2852408297/5000000000 : ℝ)^8285 ≤ (9489219061071/20000000000000 : ℝ)^6237 := by
    have hnat : (2852408297 : ℕ)^8285*20000000000000^6237 ≤ 9489219061071^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852408297 5000000000 9489219061071 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309216481/2500000000 : ℝ), (-35884933/200000000 : ℝ), (2852408297/5000000000 : ℝ)] ![(10586805281577/25000000000000 : ℝ), (1020668355439/10000000000000 : ℝ), (9489219061071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309216481/2500000000 : ℝ)|^8285 ≤ (10586805281577/25000000000000 : ℝ)^6237
        have hw : |(1309216481/2500000000 : ℝ)|=(1309216481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35884933/200000000 : ℝ)|^8285 ≤ (1020668355439/10000000000000 : ℝ)^6237
        have hw : |(-35884933/200000000 : ℝ)|=(35884933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2852408297/5000000000 : ℝ)|^8285 ≤ (9489219061071/20000000000000 : ℝ)^6237
        have hw : |(2852408297/5000000000 : ℝ)|=(2852408297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_6 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (654608243/1250000000 : ℝ)*x 0 + (1426204179/2500000000 : ℝ)*x 1 + (-1794246443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654608243/1250000000 : ℝ)^8285 ≤ (42347221341141/100000000000000 : ℝ)^6237 := by
    have hnat : (654608243 : ℕ)^8285*100000000000000^6237 ≤ 42347221341141^6237*1250000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654608243 1250000000 42347221341141 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426204179/2500000000 : ℝ)^8285 ≤ (23723048326593/50000000000000 : ℝ)^6237 := by
    have hnat : (1426204179 : ℕ)^8285*50000000000000^6237 ≤ 23723048326593^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426204179 2500000000 23723048326593 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794246443/10000000000 : ℝ)^8285 ≤ (10206681990199/100000000000000 : ℝ)^6237 := by
    have hnat : (1794246443 : ℕ)^8285*100000000000000^6237 ≤ 10206681990199^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794246443 10000000000 10206681990199 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654608243/1250000000 : ℝ), (1426204179/2500000000 : ℝ), (-1794246443/10000000000 : ℝ)] ![(42347221341141/100000000000000 : ℝ), (23723048326593/50000000000000 : ℝ), (10206681990199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654608243/1250000000 : ℝ)|^8285 ≤ (42347221341141/100000000000000 : ℝ)^6237
        have hw : |(654608243/1250000000 : ℝ)|=(654608243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426204179/2500000000 : ℝ)|^8285 ≤ (23723048326593/50000000000000 : ℝ)^6237
        have hw : |(1426204179/2500000000 : ℝ)|=(1426204179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794246443/10000000000 : ℝ)|^8285 ≤ (10206681990199/100000000000000 : ℝ)^6237
        have hw : |(-1794246443/10000000000 : ℝ)|=(1794246443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s1_7 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1080842971/2500000000 : ℝ)*x 0 + (2536457597/5000000000 : ℝ)*x 1 + (1843891879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080842971/2500000000 : ℝ)^8285 ≤ (4103460177513/12500000000000 : ℝ)^6237 := by
    have hnat : (1080842971 : ℕ)^8285*12500000000000^6237 ≤ 4103460177513^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080842971 2500000000 4103460177513 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536457597/5000000000 : ℝ)^8285 ≤ (10148809819/25000000000 : ℝ)^6237 := by
    have hnat : (2536457597 : ℕ)^8285*25000000000^6237 ≤ 10148809819^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536457597 5000000000 10148809819 25000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1843891879/5000000000 : ℝ)^8285 ≤ (26577079281383/100000000000000 : ℝ)^6237 := by
    have hnat : (1843891879 : ℕ)^8285*100000000000000^6237 ≤ 26577079281383^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843891879 5000000000 26577079281383 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080842971/2500000000 : ℝ), (2536457597/5000000000 : ℝ), (1843891879/5000000000 : ℝ)] ![(4103460177513/12500000000000 : ℝ), (10148809819/25000000000 : ℝ), (26577079281383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080842971/2500000000 : ℝ)|^8285 ≤ (4103460177513/12500000000000 : ℝ)^6237
        have hw : |(1080842971/2500000000 : ℝ)|=(1080842971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536457597/5000000000 : ℝ)|^8285 ≤ (10148809819/25000000000 : ℝ)^6237
        have hw : |(2536457597/5000000000 : ℝ)|=(2536457597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1843891879/5000000000 : ℝ)|^8285 ≤ (26577079281383/100000000000000 : ℝ)^6237
        have hw : |(1843891879/5000000000 : ℝ)|=(1843891879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1092_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1073/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5167/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3501/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (103/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3501/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (103/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3501/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (103/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3501/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (103/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3501/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (103/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3501/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (103/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (103/50000 : ℝ) ^ (2071/512 : ℝ) ≤ (681981769/50000000000000000000 : ℝ) := by
    have hpowers : (103/50000 : ℝ)^2071 ≤ (681981769/50000000000000000000 : ℝ)^512 := by
      have hnat : (103 : ℕ)^2071*50000000000000000000^512 ≤ 681981769^512*50000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103 50000 681981769 50000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (103/50000 : ℝ)) (X := (681981769/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3501/12500 : ℝ) ^ (2071/512 : ℝ) ≤ (581164752422936203/100000000000000000000 : ℝ) := by
    have hpowers : (3501/12500 : ℝ)^2071 ≤ (581164752422936203/100000000000000000000 : ℝ)^512 := by
      have hnat : (3501 : ℕ)^2071*100000000000000000000^512 ≤ 581164752422936203^512*12500^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3501 12500 581164752422936203 100000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3501/12500 : ℝ)) (X := (581164752422936203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000000681981769/25000000000000000000 : ℝ) ≤ (10000000000067441/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25000000000681981769/25000000000000000000 : ℝ)^512 ≤ (10000000000067441/10000000000000000 : ℝ)^2071 := by
      have hnat : (25000000000681981769 : ℕ)^512*10000000000000000^2071 ≤ 10000000000067441^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000000681981769 25000000000000000000 10000000000067441 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000067441/10000000000000000 : ℝ)) (X := (25000000000681981769/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100581164753786899741/100000000000000000000 : ℝ) ≤ (10014336439876549/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (100581164753786899741/100000000000000000000 : ℝ)^512 ≤ (10014336439876549/10000000000000000 : ℝ)^2071 := by
      have hnat : (100581164753786899741 : ℕ)^512*10000000000000000^2071 ≤ 10014336439876549^2071*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100581164753786899741 100000000000000000000 10014336439876549 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014336439876549/10000000000000000 : ℝ)) (X := (100581164753786899741/100000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50581164752422936203/50000000000000000000 : ℝ) ≤ (10028672879685657/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (50581164752422936203/50000000000000000000 : ℝ)^512 ≤ (10028672879685657/10000000000000000 : ℝ)^2071 := by
      have hnat : (50581164752422936203 : ℕ)^512*10000000000000000^2071 ≤ 10028672879685657^2071*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50581164752422936203 50000000000000000000 10028672879685657 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028672879685657/10000000000000000 : ℝ)) (X := (50581164752422936203/50000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(681981769/50000000000000000000 : ℝ) ≤ ((139007046694336821093/139010000000000000000 : ℝ)+2*(3584109952277/695050000000000 : ℝ)*(103/50000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (139007046694336821093/139010000000000000000 : ℝ)+2*(3584109952277/695050000000000 : ℝ)*(103/50000 : ℝ)=(10000000000067441/10000000000000000 : ℝ) by norm_num, show 1+2*(681981769/50000000000000000000 : ℝ)=(25000000000681981769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(581164752422936203/100000000000000000000 : ℝ)+(681981769/50000000000000000000 : ℝ) ≤ ((139007046694336821093/139010000000000000000 : ℝ)+(3584109952277/695050000000000 : ℝ)*((3501/12500 : ℝ)+(103/50000 : ℝ)))^(2071/512 : ℝ) := by
    rw [show (139007046694336821093/139010000000000000000 : ℝ)+(3584109952277/695050000000000 : ℝ)*((3501/12500 : ℝ)+(103/50000 : ℝ))=(10014336439876549/10000000000000000 : ℝ) by norm_num, show 1+(581164752422936203/100000000000000000000 : ℝ)+(681981769/50000000000000000000 : ℝ)=(100581164753786899741/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(581164752422936203/100000000000000000000 : ℝ) ≤ ((139007046694336821093/139010000000000000000 : ℝ)+2*(3584109952277/695050000000000 : ℝ)*(3501/12500 : ℝ))^(2071/512 : ℝ) := by
    rw [show (139007046694336821093/139010000000000000000 : ℝ)+2*(3584109952277/695050000000000 : ℝ)*(3501/12500 : ℝ)=(10028672879685657/10000000000000000 : ℝ) by norm_num, show 1+2*(581164752422936203/100000000000000000000 : ℝ)=(50581164752422936203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139007046694336821093/139010000000000000000 : ℝ)*(X 1 0+X 2 0)+(3584109952277/695050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (103/50000 : ℝ)) (hi := (3501/12500 : ℝ)) (c := (139007046694336821093/139010000000000000000 : ℝ)) (alpha := (3584109952277/695050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139007046694336821093/139010000000000000000 : ℝ)*(X 0 1+X 2 1)+(3584109952277/695050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (103/50000 : ℝ)) (hi := (3501/12500 : ℝ)) (c := (139007046694336821093/139010000000000000000 : ℝ)) (alpha := (3584109952277/695050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139007046694336821093/139010000000000000000 : ℝ)*(X 0 2+X 1 2)+(3584109952277/695050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (103/50000 : ℝ)) (hi := (3501/12500 : ℝ)) (c := (139007046694336821093/139010000000000000000 : ℝ)) (alpha := (3584109952277/695050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529001119/2500000000 : ℝ)*X 0 0+(1428771943/2500000000 : ℝ)*X 0 1+(2495814727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421876433/10000000000 : ℝ)*X 1 0+(-2507434007/10000000000 : ℝ)*X 1 1+(998325931/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355469341/2500000000 : ℝ)*X 2 0+(499162871/1000000000 : ℝ)*X 2 1+(-2507433993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321641873/10000000000 : ℝ)*X 0 0+(3667550771/10000000000 : ℝ)*X 0 1+(5092748971/10000000000 : ℝ)*X 0 2+(4321641873/10000000000 : ℝ)*X 1 0+(3667550771/10000000000 : ℝ)*X 1 1+(5092748971/10000000000 : ℝ)*X 1 2+(4321641873/10000000000 : ℝ)*X 2 0+(3667550771/10000000000 : ℝ)*X 2 1+(5092748971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058441553/5000000000 : ℝ)*X 0 0+(1250424461/2500000000 : ℝ)*X 0 1+(5704816753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309216481/2500000000 : ℝ)*X 1 0+(-35884933/200000000 : ℝ)*X 1 1+(2852408297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((654608243/1250000000 : ℝ)*X 2 0+(1426204179/2500000000 : ℝ)*X 2 1+(-1794246443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080842971/2500000000 : ℝ)*X 0 0+(2536457597/5000000000 : ℝ)*X 0 1+(1843891879/5000000000 : ℝ)*X 0 2+(1080842971/2500000000 : ℝ)*X 1 0+(2536457597/5000000000 : ℝ)*X 1 1+(1843891879/5000000000 : ℝ)*X 1 2+(1080842971/2500000000 : ℝ)*X 2 0+(2536457597/5000000000 : ℝ)*X 2 1+(1843891879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16787880295428115659019149327/3475250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38401057/25000000000000 : ℝ)*(base1) + (233349693/25000000000000 : ℝ)*(base19) + (36585893/3125000000000 : ℝ)*(base23) + (62436499/100000000000000 : ℝ)*(upper3) + (32867757/25000000000000 : ℝ)*(upper5) + (520979718617313/50000000000000 : ℝ)*(major0) + (520979718617313/50000000000000 : ℝ)*(major1) + (520979718617313/50000000000000 : ℝ)*(major2) + (1382253377336779/100000000000000 : ℝ)*(sp0) + (34556432104239/2500000000000 : ℝ)*(sp1) + (276451409363951/20000000000000 : ℝ)*(sp2) + (21926830309251/3125000000000 : ℝ)*(sp3) + (4993835781/100000000000000 : ℝ)*(sp4) + (354475483/20000000000000 : ℝ)*(sp7) + (175415123969419/25000000000000 : ℝ)*(f.failure) + (1382258217568331/100000000000000 : ℝ)*(f.sum) + (49306730261887/34752500000000000000000000000 : ℝ)*base65 + (16681870777486583109/6950500000000000000000000000000000 : ℝ)*base67 + (30612317622996916891/6950500000000000000000000000000000 : ℝ)*base70 + (27944652299684416891/6950500000000000000000000000000000 : ℝ)*base72 + (140551224195747/34752500000000000000000000000 : ℝ)*base73 + (33606412594967416891/6950500000000000000000000000000000 : ℝ)*base76 + (3496590635854416891/6950500000000000000000000000000000 : ℝ)*base78 + (40684425144637583109/6950500000000000000000000000000000 : ℝ)*base79 + (155939407924331/69505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (711867/156250000000000000000 : ℝ)*base89 + (711867/156250000000000000000 : ℝ)*base91 + (711867/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25448326199620334157258910989/3475250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21501471/25000000000000 : ℝ)*(base1) + (1636095739/100000000000000 : ℝ)*(base19) + (1656130413/100000000000000 : ℝ)*(base23) + (83011639/50000000000000 : ℝ)*(upper3) + (166073471/100000000000000 : ℝ)*(upper5) + (1072094005229491/100000000000000 : ℝ)*(major0) + (1072094005229491/100000000000000 : ℝ)*(major1) + (1072094005229491/100000000000000 : ℝ)*(major2) + (6520471893/100000000000000 : ℝ)*(sp1) + (6933788561/100000000000000 : ℝ)*(sp2) + (711117296744729/50000000000000 : ℝ)*(sp4) + (1422226350915943/100000000000000 : ℝ)*(sp5) + (1422225917564601/100000000000000 : ℝ)*(sp6) + (360976586439217/50000000000000 : ℝ)*(sp7) + (360976629442159/50000000000000 : ℝ)*(f.failure) + (56889380299343/4000000000000 : ℝ)*(f.sum) + (30977543134763/34752500000000000000000000000 : ℝ)*base66 + (47260985952872146337/13901000000000000000000000000000000 : ℝ)*base68 + (34508725974829853663/13901000000000000000000000000000000 : ℝ)*base69 + (70054718506881146337/13901000000000000000000000000000000 : ℝ)*base72 + (306756345250461/69505000000000000000000000000 : ℝ)*base74 + (100206632124053146337/13901000000000000000000000000000000 : ℝ)*base76 + (59827162667728146337/13901000000000000000000000000000000 : ℝ)*base78 + (122834162709546146337/13901000000000000000000000000000000 : ℝ)*base80 + (16129347313367/34752500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (640687/312500000000000000000 : ℝ)*base89 + (640687/312500000000000000000 : ℝ)*base91 + (640687/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1092_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1073/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5167/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1092_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1092_s2_0 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542992139/2500000000 : ℝ)*x 0 + (2760299069/5000000000 : ℝ)*x 1 + (206023411/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542992139/2500000000 : ℝ)^8285 ≤ (6577650262719/50000000000000 : ℝ)^6237 := by
    have hnat : (542992139 : ℕ)^8285*50000000000000^6237 ≤ 6577650262719^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542992139 2500000000 6577650262719 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760299069/5000000000 : ℝ)^8285 ≤ (45421756943559/100000000000000 : ℝ)^6237 := by
    have hnat : (2760299069 : ℕ)^8285*100000000000000^6237 ≤ 45421756943559^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760299069 5000000000 45421756943559 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206023411/400000000 : ℝ)^8285 ≤ (20711471257607/50000000000000 : ℝ)^6237 := by
    have hnat : (206023411 : ℕ)^8285*50000000000000^6237 ≤ 20711471257607^6237*400000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206023411 400000000 20711471257607 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542992139/2500000000 : ℝ), (2760299069/5000000000 : ℝ), (206023411/400000000 : ℝ)] ![(6577650262719/50000000000000 : ℝ), (45421756943559/100000000000000 : ℝ), (20711471257607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542992139/2500000000 : ℝ)|^8285 ≤ (6577650262719/50000000000000 : ℝ)^6237
        have hw : |(-542992139/2500000000 : ℝ)|=(542992139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760299069/5000000000 : ℝ)|^8285 ≤ (45421756943559/100000000000000 : ℝ)^6237
        have hw : |(2760299069/5000000000 : ℝ)|=(2760299069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206023411/400000000 : ℝ)|^8285 ≤ (20711471257607/50000000000000 : ℝ)^6237
        have hw : |(206023411/400000000 : ℝ)|=(206023411/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_1 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5376045131/10000000000 : ℝ)*x 0 + (-236472537/1000000000 : ℝ)*x 1 + (2575293149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376045131/10000000000 : ℝ)^8285 ≤ (21924358895409/50000000000000 : ℝ)^6237 := by
    have hnat : (5376045131 : ℕ)^8285*50000000000000^6237 ≤ 21924358895409^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376045131 10000000000 21924358895409 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236472537/1000000000 : ℝ)^8285 ≤ (294566574933/2000000000000 : ℝ)^6237 := by
    have hnat : (236472537 : ℕ)^8285*2000000000000^6237 ≤ 294566574933^6237*1000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236472537 1000000000 294566574933 2000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575293149/5000000000 : ℝ)^8285 ≤ (20711476722061/50000000000000 : ℝ)^6237 := by
    have hnat : (2575293149 : ℕ)^8285*50000000000000^6237 ≤ 20711476722061^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575293149 5000000000 20711476722061 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376045131/10000000000 : ℝ), (-236472537/1000000000 : ℝ), (2575293149/5000000000 : ℝ)] ![(21924358895409/50000000000000 : ℝ), (294566574933/2000000000000 : ℝ), (20711476722061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376045131/10000000000 : ℝ)|^8285 ≤ (21924358895409/50000000000000 : ℝ)^6237
        have hw : |(5376045131/10000000000 : ℝ)|=(5376045131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236472537/1000000000 : ℝ)|^8285 ≤ (294566574933/2000000000000 : ℝ)^6237
        have hw : |(-236472537/1000000000 : ℝ)|=(236472537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575293149/5000000000 : ℝ)|^8285 ≤ (20711476722061/50000000000000 : ℝ)^6237
        have hw : |(2575293149/5000000000 : ℝ)|=(2575293149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_2 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688022539/5000000000 : ℝ)*x 0 + (1030117269/2000000000 : ℝ)*x 1 + (-2364725379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688022539/5000000000 : ℝ)^8285 ≤ (43848717216587/100000000000000 : ℝ)^6237 := by
    have hnat : (2688022539 : ℕ)^8285*100000000000000^6237 ≤ 43848717216587^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688022539 5000000000 43848717216587 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030117269/2000000000 : ℝ)^8285 ≤ (41422953946233/100000000000000 : ℝ)^6237 := by
    have hnat : (1030117269 : ℕ)^8285*100000000000000^6237 ≤ 41422953946233^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030117269 2000000000 41422953946233 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364725379/10000000000 : ℝ)^8285 ≤ (1841041102639/12500000000000 : ℝ)^6237 := by
    have hnat : (2364725379 : ℕ)^8285*12500000000000^6237 ≤ 1841041102639^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364725379 10000000000 1841041102639 12500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688022539/5000000000 : ℝ), (1030117269/2000000000 : ℝ), (-2364725379/10000000000 : ℝ)] ![(43848717216587/100000000000000 : ℝ), (41422953946233/100000000000000 : ℝ), (1841041102639/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688022539/5000000000 : ℝ)|^8285 ≤ (43848717216587/100000000000000 : ℝ)^6237
        have hw : |(2688022539/5000000000 : ℝ)|=(2688022539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030117269/2000000000 : ℝ)|^8285 ≤ (41422953946233/100000000000000 : ℝ)^6237
        have hw : |(1030117269/2000000000 : ℝ)|=(1030117269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2364725379/10000000000 : ℝ)|^8285 ≤ (1841041102639/12500000000000 : ℝ)^6237
        have hw : |(-2364725379/10000000000 : ℝ)|=(2364725379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_3 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089975177/2500000000 : ℝ)*x 0 + (1002678279/2500000000 : ℝ)*x 1 + (1184907529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089975177/2500000000 : ℝ)^8285 ≤ (8299158589979/25000000000000 : ℝ)^6237 := by
    have hnat : (1089975177 : ℕ)^8285*25000000000000^6237 ≤ 8299158589979^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089975177 2500000000 8299158589979 25000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002678279/2500000000 : ℝ)^8285 ≤ (29712161971807/100000000000000 : ℝ)^6237 := by
    have hnat : (1002678279 : ℕ)^8285*100000000000000^6237 ≤ 29712161971807^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002678279 2500000000 29712161971807 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184907529/2500000000 : ℝ)^8285 ≤ (18545601826411/50000000000000 : ℝ)^6237 := by
    have hnat : (1184907529 : ℕ)^8285*50000000000000^6237 ≤ 18545601826411^6237*2500000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184907529 2500000000 18545601826411 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089975177/2500000000 : ℝ), (1002678279/2500000000 : ℝ), (1184907529/2500000000 : ℝ)] ![(8299158589979/25000000000000 : ℝ), (29712161971807/100000000000000 : ℝ), (18545601826411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089975177/2500000000 : ℝ)|^8285 ≤ (8299158589979/25000000000000 : ℝ)^6237
        have hw : |(1089975177/2500000000 : ℝ)|=(1089975177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002678279/2500000000 : ℝ)|^8285 ≤ (29712161971807/100000000000000 : ℝ)^6237
        have hw : |(1002678279/2500000000 : ℝ)|=(1002678279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184907529/2500000000 : ℝ)|^8285 ≤ (18545601826411/50000000000000 : ℝ)^6237
        have hw : |(1184907529/2500000000 : ℝ)|=(1184907529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_4 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086042877/5000000000 : ℝ)*x 0 + (161038379/312500000 : ℝ)*x 1 + (689741013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086042877/5000000000 : ℝ)^8285 ≤ (13156243474117/100000000000000 : ℝ)^6237 := by
    have hnat : (1086042877 : ℕ)^8285*100000000000000^6237 ≤ 13156243474117^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086042877 5000000000 13156243474117 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161038379/312500000 : ℝ)^8285 ≤ (8290235801197/20000000000000 : ℝ)^6237 := by
    have hnat : (161038379 : ℕ)^8285*20000000000000^6237 ≤ 8290235801197^6237*312500000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161038379 312500000 8290235801197 20000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689741013/1250000000 : ℝ)^8285 ≤ (4539257750953/10000000000000 : ℝ)^6237 := by
    have hnat : (689741013 : ℕ)^8285*10000000000000^6237 ≤ 4539257750953^6237*1250000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689741013 1250000000 4539257750953 10000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086042877/5000000000 : ℝ), (161038379/312500000 : ℝ), (689741013/1250000000 : ℝ)] ![(13156243474117/100000000000000 : ℝ), (8290235801197/20000000000000 : ℝ), (4539257750953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086042877/5000000000 : ℝ)|^8285 ≤ (13156243474117/100000000000000 : ℝ)^6237
        have hw : |(-1086042877/5000000000 : ℝ)|=(1086042877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161038379/312500000 : ℝ)|^8285 ≤ (8290235801197/20000000000000 : ℝ)^6237
        have hw : |(161038379/312500000 : ℝ)|=(161038379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689741013/1250000000 : ℝ)|^8285 ≤ (4539257750953/10000000000000 : ℝ)^6237
        have hw : |(689741013/1250000000 : ℝ)|=(689741013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_5 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641240521/5000000000 : ℝ)*x 0 + (-1997383061/10000000000 : ℝ)*x 1 + (1103585639/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641240521/5000000000 : ℝ)^8285 ≤ (1070947531131/2500000000000 : ℝ)^6237 := by
    have hnat : (2641240521 : ℕ)^8285*2500000000000^6237 ≤ 1070947531131^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641240521 5000000000 1070947531131 2500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997383061/10000000000 : ℝ)^8285 ≤ (11769520246261/100000000000000 : ℝ)^6237 := by
    have hnat : (1997383061 : ℕ)^8285*100000000000000^6237 ≤ 11769520246261^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997383061 10000000000 11769520246261 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103585639/2000000000 : ℝ)^8285 ≤ (45392578503943/100000000000000 : ℝ)^6237 := by
    have hnat : (1103585639 : ℕ)^8285*100000000000000^6237 ≤ 45392578503943^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103585639 2000000000 45392578503943 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641240521/5000000000 : ℝ), (-1997383061/10000000000 : ℝ), (1103585639/2000000000 : ℝ)] ![(1070947531131/2500000000000 : ℝ), (11769520246261/100000000000000 : ℝ), (45392578503943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641240521/5000000000 : ℝ)|^8285 ≤ (1070947531131/2500000000000 : ℝ)^6237
        have hw : |(2641240521/5000000000 : ℝ)|=(2641240521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997383061/10000000000 : ℝ)|^8285 ≤ (11769520246261/100000000000000 : ℝ)^6237
        have hw : |(-1997383061/10000000000 : ℝ)|=(1997383061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103585639/2000000000 : ℝ)|^8285 ≤ (45392578503943/100000000000000 : ℝ)^6237
        have hw : |(1103585639/2000000000 : ℝ)|=(1103585639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_6 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2641240613/5000000000 : ℝ)*x 0 + (2758964057/5000000000 : ℝ)*x 1 + (-1997382919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641240613/5000000000 : ℝ)^8285 ≤ (42837903227337/100000000000000 : ℝ)^6237 := by
    have hnat : (2641240613 : ℕ)^8285*100000000000000^6237 ≤ 42837903227337^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641240613 5000000000 42837903227337 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758964057/5000000000 : ℝ)^8285 ≤ (22696288809403/50000000000000 : ℝ)^6237 := by
    have hnat : (2758964057 : ℕ)^8285*50000000000000^6237 ≤ 22696288809403^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758964057 5000000000 22696288809403 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997382919/10000000000 : ℝ)^8285 ≤ (5884759567389/50000000000000 : ℝ)^6237 := by
    have hnat : (1997382919 : ℕ)^8285*50000000000000^6237 ≤ 5884759567389^6237*10000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997382919 10000000000 5884759567389 50000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641240613/5000000000 : ℝ), (2758964057/5000000000 : ℝ), (-1997382919/10000000000 : ℝ)] ![(42837903227337/100000000000000 : ℝ), (22696288809403/50000000000000 : ℝ), (5884759567389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641240613/5000000000 : ℝ)|^8285 ≤ (42837903227337/100000000000000 : ℝ)^6237
        have hw : |(2641240613/5000000000 : ℝ)|=(2641240613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758964057/5000000000 : ℝ)|^8285 ≤ (22696288809403/50000000000000 : ℝ)^6237
        have hw : |(2758964057/5000000000 : ℝ)|=(2758964057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997382919/10000000000 : ℝ)|^8285 ≤ (5884759567389/50000000000000 : ℝ)^6237
        have hw : |(-1997382919/10000000000 : ℝ)|=(1997382919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1092_s2_7 (p : ℝ) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180066469/5000000000 : ℝ)*x 0 + (946884859/2000000000 : ℝ)*x 1 + (125499111/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180066469/5000000000 : ℝ)^8285 ≤ (33198983215659/100000000000000 : ℝ)^6237 := by
    have hnat : (2180066469 : ℕ)^8285*100000000000000^6237 ≤ 33198983215659^6237*5000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180066469 5000000000 33198983215659 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946884859/2000000000 : ℝ)^8285 ≤ (925927414207/2500000000000 : ℝ)^6237 := by
    have hnat : (946884859 : ℕ)^8285*2500000000000^6237 ≤ 925927414207^6237*2000000000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946884859 2000000000 925927414207 2500000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125499111/312500000 : ℝ)^8285 ≤ (29763920207597/100000000000000 : ℝ)^6237 := by
    have hnat : (125499111 : ℕ)^8285*100000000000000^6237 ≤ 29763920207597^6237*312500000^8285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125499111 312500000 29763920207597 100000000000000 8285 6237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8285/2048 : ℝ)) 8285 6237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180066469/5000000000 : ℝ), (946884859/2000000000 : ℝ), (125499111/312500000 : ℝ)] ![(33198983215659/100000000000000 : ℝ), (925927414207/2500000000000 : ℝ), (29763920207597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180066469/5000000000 : ℝ)|^8285 ≤ (33198983215659/100000000000000 : ℝ)^6237
        have hw : |(2180066469/5000000000 : ℝ)|=(2180066469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(946884859/2000000000 : ℝ)|^8285 ≤ (925927414207/2500000000000 : ℝ)^6237
        have hw : |(946884859/2000000000 : ℝ)|=(946884859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125499111/312500000 : ℝ)|^8285 ≤ (29763920207597/100000000000000 : ℝ)^6237
        have hw : |(125499111/312500000 : ℝ)|=(125499111/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1092_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5167/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4419/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16657/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5167/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1073/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5167/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1073/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5167/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1073/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5167/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1073/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5167/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1073/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5167/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1073/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1073/20000 : ℝ) ^ (2071/512 : ℝ) ≤ (726455130486941/100000000000000000000 : ℝ) := by
    have hpowers : (1073/20000 : ℝ)^2071 ≤ (726455130486941/100000000000000000000 : ℝ)^512 := by
      have hnat : (1073 : ℕ)^2071*100000000000000000000^512 ≤ 726455130486941^512*20000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1073 20000 726455130486941 100000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1073/20000 : ℝ)) (X := (726455130486941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hpowhi : (5167/25000 : ℝ) ^ (2071/512 : ℝ) ≤ (169994838089375167/100000000000000000000 : ℝ) := by
    have hpowers : (5167/25000 : ℝ)^2071 ≤ (169994838089375167/100000000000000000000 : ℝ)^512 := by
      have hnat : (5167 : ℕ)^2071*100000000000000000000^512 ≤ 169994838089375167^512*25000^2071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5167 25000 169994838089375167 100000000000000000000 2071 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5167/25000 : ℝ)) (X := (169994838089375167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000726455130486941/50000000000000000000 : ℝ) ≤ (1000003591916879/1000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (50000726455130486941/50000000000000000000 : ℝ)^512 ≤ (1000003591916879/1000000000000000 : ℝ)^2071 := by
      have hnat : (50000726455130486941 : ℕ)^512*1000000000000000^2071 ≤ 1000003591916879^2071*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000726455130486941 50000000000000000000 1000003591916879 1000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000003591916879/1000000000000000 : ℝ)) (X := (50000726455130486941/50000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25042680323304965527/25000000000000000000 : ℝ) ≤ (10004217923277117/10000000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (25042680323304965527/25000000000000000000 : ℝ)^512 ≤ (10004217923277117/10000000000000000 : ℝ)^2071 := by
      have hnat : (25042680323304965527 : ℕ)^512*10000000000000000^2071 ≤ 10004217923277117^2071*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25042680323304965527 25000000000000000000 10004217923277117 10000000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004217923277117/10000000000000000 : ℝ)) (X := (25042680323304965527/25000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50169994838089375167/50000000000000000000 : ℝ) ≤ (2502099981846361/2500000000000000 : ℝ) ^ (2071/512 : ℝ) := by
    have hpowers : (50169994838089375167/50000000000000000000 : ℝ)^512 ≤ (2502099981846361/2500000000000000 : ℝ)^2071 := by
      have hnat : (50169994838089375167 : ℕ)^512*2500000000000000^2071 ≤ 2502099981846361^2071*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50169994838089375167 50000000000000000000 2502099981846361 2500000000000000 512 2071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502099981846361/2500000000000000 : ℝ)) (X := (50169994838089375167/50000000000000000000 : ℝ)) (by norm_num) 2071 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(726455130486941/100000000000000000000 : ℝ) ≤ ((7649283838347882233/7651500000000000000 : ℝ)+2*(4182004108327/1530300000000000 : ℝ)*(1073/20000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (7649283838347882233/7651500000000000000 : ℝ)+2*(4182004108327/1530300000000000 : ℝ)*(1073/20000 : ℝ)=(1000003591916879/1000000000000000 : ℝ) by norm_num, show 1+2*(726455130486941/100000000000000000000 : ℝ)=(50000726455130486941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(169994838089375167/100000000000000000000 : ℝ)+(726455130486941/100000000000000000000 : ℝ) ≤ ((7649283838347882233/7651500000000000000 : ℝ)+(4182004108327/1530300000000000 : ℝ)*((5167/25000 : ℝ)+(1073/20000 : ℝ)))^(2071/512 : ℝ) := by
    rw [show (7649283838347882233/7651500000000000000 : ℝ)+(4182004108327/1530300000000000 : ℝ)*((5167/25000 : ℝ)+(1073/20000 : ℝ))=(10004217923277117/10000000000000000 : ℝ) by norm_num, show 1+(169994838089375167/100000000000000000000 : ℝ)+(726455130486941/100000000000000000000 : ℝ)=(25042680323304965527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(169994838089375167/100000000000000000000 : ℝ) ≤ ((7649283838347882233/7651500000000000000 : ℝ)+2*(4182004108327/1530300000000000 : ℝ)*(5167/25000 : ℝ))^(2071/512 : ℝ) := by
    rw [show (7649283838347882233/7651500000000000000 : ℝ)+2*(4182004108327/1530300000000000 : ℝ)*(5167/25000 : ℝ)=(2502099981846361/2500000000000000 : ℝ) by norm_num, show 1+2*(169994838089375167/100000000000000000000 : ℝ)=(50169994838089375167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7649283838347882233/7651500000000000000 : ℝ)*(X 1 0+X 2 0)+(4182004108327/1530300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (1073/20000 : ℝ)) (hi := (5167/25000 : ℝ)) (c := (7649283838347882233/7651500000000000000 : ℝ)) (alpha := (4182004108327/1530300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7649283838347882233/7651500000000000000 : ℝ)*(X 0 1+X 2 1)+(4182004108327/1530300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (1073/20000 : ℝ)) (hi := (5167/25000 : ℝ)) (c := (7649283838347882233/7651500000000000000 : ℝ)) (alpha := (4182004108327/1530300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7649283838347882233/7651500000000000000 : ℝ)*(X 0 2+X 1 2)+(4182004108327/1530300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2071/512 : ℝ)) (lo := (1073/20000 : ℝ)) (hi := (5167/25000 : ℝ)) (c := (7649283838347882233/7651500000000000000 : ℝ)) (alpha := (4182004108327/1530300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-542992139/2500000000 : ℝ)*X 0 0+(2760299069/5000000000 : ℝ)*X 0 1+(206023411/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376045131/10000000000 : ℝ)*X 1 0+(-236472537/1000000000 : ℝ)*X 1 1+(2575293149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688022539/5000000000 : ℝ)*X 2 0+(1030117269/2000000000 : ℝ)*X 2 1+(-2364725379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089975177/2500000000 : ℝ)*X 0 0+(1002678279/2500000000 : ℝ)*X 0 1+(1184907529/2500000000 : ℝ)*X 0 2+(1089975177/2500000000 : ℝ)*X 1 0+(1002678279/2500000000 : ℝ)*X 1 1+(1184907529/2500000000 : ℝ)*X 1 2+(1089975177/2500000000 : ℝ)*X 2 0+(1002678279/2500000000 : ℝ)*X 2 1+(1184907529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1086042877/5000000000 : ℝ)*X 0 0+(161038379/312500000 : ℝ)*X 0 1+(689741013/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2641240521/5000000000 : ℝ)*X 1 0+(-1997383061/10000000000 : ℝ)*X 1 1+(1103585639/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641240613/5000000000 : ℝ)*X 2 0+(2758964057/5000000000 : ℝ)*X 2 1+(-1997382919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180066469/5000000000 : ℝ)*X 0 0+(946884859/2000000000 : ℝ)*X 0 1+(125499111/312500000 : ℝ)*X 0 2+(2180066469/5000000000 : ℝ)*X 1 0+(946884859/2000000000 : ℝ)*X 1 1+(125499111/312500000 : ℝ)*X 1 2+(2180066469/5000000000 : ℝ)*X 2 0+(946884859/2000000000 : ℝ)*X 2 1+(125499111/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1092_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (279249745643485032267378919/63762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20599671/10000000000000 : ℝ)*(base19) + (70840641/100000000000000 : ℝ)*(base23) + (50838703/100000000000000 : ℝ)*(upper2) + (94761867/100000000000000 : ℝ)*(upper3) + (109175303/100000000000000 : ℝ)*(upper4) + (1018632234853843/50000000000000 : ℝ)*(major0) + (1018632234853843/50000000000000 : ℝ)*(major1) + (1018632234853843/50000000000000 : ℝ)*(major2) + (675654358997067/25000000000000 : ℝ)*(sp0) + (1351312448104593/50000000000000 : ℝ)*(sp1) + (337828128920657/12500000000000 : ℝ)*(sp2) + (1371900563769403/100000000000000 : ℝ)*(sp3) + (1916554407/25000000000000 : ℝ)*(sp4) + (3127455749/100000000000000 : ℝ)*(sp7) + (1371903691225151/100000000000000 : ℝ)*(f.failure) + (337828137775737/12500000000000 : ℝ)*(f.sum) + (103433004172271/9564375000000000000000000000 : ℝ)*base66 + (741737338646951419/382575000000000000000000000000000 : ℝ)*base67 + (1144486613709176419/382575000000000000000000000000000 : ℝ)*base69 + (928307431149123581/382575000000000000000000000000000 : ℝ)*base72 + (424684292491423/76515000000000000000000000000 : ℝ)*base74 + (1303366887592023581/382575000000000000000000000000000 : ℝ)*base76 + (2988946899159273581/382575000000000000000000000000000 : ℝ)*base78 + (3761684573789448581/382575000000000000000000000000000 : ℝ)*base80 + (117677722787129/38257500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4614857/625000000000000000000 : ℝ)*base90 + (4614857/625000000000000000000 : ℝ)*base92 + (4614857/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57942637042436940667287411/6376250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1801320419/100000000000000 : ℝ)*(base19) + (1032444771/50000000000000 : ℝ)*(base23) + (47893899/20000000000000 : ℝ)*(upper3) + (59491813/100000000000000 : ℝ)*(lower4) + (11370551/6250000000000 : ℝ)*(upper5) + (206692980360417/10000000000000 : ℝ)*(major0) + (206692980360417/10000000000000 : ℝ)*(major1) + (206692980360417/10000000000000 : ℝ)*(major2) + (3227768259/20000000000000 : ℝ)*(sp1) + (19268905511/100000000000000 : ℝ)*(sp2) + (2741978834566323/100000000000000 : ℝ)*(sp4) + (1338848092971/48828125000 : ℝ)*(sp5) + (274195750077127/10000000000000 : ℝ)*(sp6) + (139188046973337/10000000000000 : ℝ)*(sp7) + (139188046973337/10000000000000 : ℝ)*(f.failure) + (2741978834566323/100000000000000 : ℝ)*(f.sum) + (4215024531353/1275250000000000000000000000 : ℝ)*base66 + (45293110393614613/25505000000000000000000000000000 : ℝ)*base68 + (66846731384304613/25505000000000000000000000000000 : ℝ)*base70 + (30729394509150387/25505000000000000000000000000000 : ℝ)*base71 + (911803490603/2550500000000000000000000000 : ℝ)*base74 + (156396237057694613/25505000000000000000000000000000 : ℝ)*base76 + (110820185142834613/25505000000000000000000000000000 : ℝ)*base78 + (73430194027769613/25505000000000000000000000000000 : ℝ)*base80 + (2904035591273/1020200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (301041/62500000000000000000 : ℝ)*base89 + (301041/62500000000000000000 : ℝ)*base91 + (301041/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1092_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5167/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1092_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1092_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1092_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1092_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1092_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2071/512 : ℝ) ≤ p) (hpb : p ≤ (8285/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9281193/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4419/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16657/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1092_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
