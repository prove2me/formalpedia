-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1556_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:22:22.811651+00:00
-- url     : https://prove2.me/submissions/a353e804-56e7-46b9-9c02-e79f04786dae

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
theorem support_rectangle_w1556_s0_0 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1640145407/10000000000 : ℝ)*x 0 + (5879745331/10000000000 : ℝ)*x 1 + (4873691461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640145407/10000000000 : ℝ)^4609 ≤ (611653708339/6250000000000 : ℝ)^3585 := by
    have hnat : (1640145407 : ℕ)^4609*6250000000000^3585 ≤ 611653708339^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640145407 10000000000 611653708339 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5879745331/10000000000 : ℝ)^4609 ≤ (6315232492029/12500000000000 : ℝ)^3585 := by
    have hnat : (5879745331 : ℕ)^4609*12500000000000^3585 ≤ 6315232492029^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5879745331 10000000000 6315232492029 12500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4873691461/10000000000 : ℝ)^4609 ≤ (2480730044617/6250000000000 : ℝ)^3585 := by
    have hnat : (4873691461 : ℕ)^4609*6250000000000^3585 ≤ 2480730044617^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873691461 10000000000 2480730044617 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1640145407/10000000000 : ℝ), (5879745331/10000000000 : ℝ), (4873691461/10000000000 : ℝ)] ![(611653708339/6250000000000 : ℝ), (6315232492029/12500000000000 : ℝ), (2480730044617/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1640145407/10000000000 : ℝ)|^4609 ≤ (611653708339/6250000000000 : ℝ)^3585
        have hw : |(-1640145407/10000000000 : ℝ)|=(1640145407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5879745331/10000000000 : ℝ)|^4609 ≤ (6315232492029/12500000000000 : ℝ)^3585
        have hw : |(5879745331/10000000000 : ℝ)|=(5879745331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4873691461/10000000000 : ℝ)|^4609 ≤ (2480730044617/6250000000000 : ℝ)^3585
        have hw : |(4873691461/10000000000 : ℝ)|=(4873691461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_1 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2734236413/5000000000 : ℝ)*x 0 + (-1100474053/5000000000 : ℝ)*x 1 + (4873691461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734236413/5000000000 : ℝ)^4609 ≤ (23012380279117/50000000000000 : ℝ)^3585 := by
    have hnat : (2734236413 : ℕ)^4609*50000000000000^3585 ≤ 23012380279117^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734236413 5000000000 23012380279117 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100474053/5000000000 : ℝ)^4609 ≤ (14283558715599/100000000000000 : ℝ)^3585 := by
    have hnat : (1100474053 : ℕ)^4609*100000000000000^3585 ≤ 14283558715599^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100474053 5000000000 14283558715599 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4873691461/10000000000 : ℝ)^4609 ≤ (2480730044617/6250000000000 : ℝ)^3585 := by
    have hnat : (4873691461 : ℕ)^4609*6250000000000^3585 ≤ 2480730044617^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873691461 10000000000 2480730044617 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734236413/5000000000 : ℝ), (-1100474053/5000000000 : ℝ), (4873691461/10000000000 : ℝ)] ![(23012380279117/50000000000000 : ℝ), (14283558715599/100000000000000 : ℝ), (2480730044617/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734236413/5000000000 : ℝ)|^4609 ≤ (23012380279117/50000000000000 : ℝ)^3585
        have hw : |(2734236413/5000000000 : ℝ)|=(2734236413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100474053/5000000000 : ℝ)|^4609 ≤ (14283558715599/100000000000000 : ℝ)^3585
        have hw : |(-1100474053/5000000000 : ℝ)|=(1100474053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4873691461/10000000000 : ℝ)|^4609 ≤ (2480730044617/6250000000000 : ℝ)^3585
        have hw : |(4873691461/10000000000 : ℝ)|=(4873691461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_2 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2734236433/5000000000 : ℝ)*x 0 + (974738283/2000000000 : ℝ)*x 1 + (-137559257/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734236433/5000000000 : ℝ)^4609 ≤ (46024760991049/100000000000000 : ℝ)^3585 := by
    have hnat : (2734236433 : ℕ)^4609*100000000000000^3585 ≤ 46024760991049^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734236433 5000000000 46024760991049 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974738283/2000000000 : ℝ)^4609 ≤ (19845840116119/50000000000000 : ℝ)^3585 := by
    have hnat : (974738283 : ℕ)^4609*50000000000000^3585 ≤ 19845840116119^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974738283 2000000000 19845840116119 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137559257/625000000 : ℝ)^4609 ≤ (714177938283/5000000000000 : ℝ)^3585 := by
    have hnat : (137559257 : ℕ)^4609*5000000000000^3585 ≤ 714177938283^3585*625000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137559257 625000000 714177938283 5000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734236433/5000000000 : ℝ), (974738283/2000000000 : ℝ), (-137559257/625000000 : ℝ)] ![(46024760991049/100000000000000 : ℝ), (19845840116119/50000000000000 : ℝ), (714177938283/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734236433/5000000000 : ℝ)|^4609 ≤ (46024760991049/100000000000000 : ℝ)^3585
        have hw : |(2734236433/5000000000 : ℝ)|=(2734236433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(974738283/2000000000 : ℝ)|^4609 ≤ (19845840116119/50000000000000 : ℝ)^3585
        have hw : |(974738283/2000000000 : ℝ)|=(974738283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137559257/625000000 : ℝ)|^4609 ≤ (714177938283/5000000000000 : ℝ)^3585
        have hw : |(-137559257/625000000 : ℝ)|=(137559257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_3 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4133481407/10000000000 : ℝ)*x 0 + (96639221/312500000 : ℝ)*x 1 + (5444674779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133481407/10000000000 : ℝ)^4609 ≤ (16058041205897/50000000000000 : ℝ)^3585 := by
    have hnat : (4133481407 : ℕ)^4609*50000000000000^3585 ≤ 16058041205897^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133481407 10000000000 16058041205897 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96639221/312500000 : ℝ)^4609 ≤ (4423300204853/20000000000000 : ℝ)^3585 := by
    have hnat : (96639221 : ℕ)^4609*20000000000000^3585 ≤ 4423300204853^3585*312500000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96639221 312500000 4423300204853 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444674779/10000000000 : ℝ)^4609 ≤ (45767416551871/100000000000000 : ℝ)^3585 := by
    have hnat : (5444674779 : ℕ)^4609*100000000000000^3585 ≤ 45767416551871^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444674779 10000000000 45767416551871 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133481407/10000000000 : ℝ), (96639221/312500000 : ℝ), (5444674779/10000000000 : ℝ)] ![(16058041205897/50000000000000 : ℝ), (4423300204853/20000000000000 : ℝ), (45767416551871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133481407/10000000000 : ℝ)|^4609 ≤ (16058041205897/50000000000000 : ℝ)^3585
        have hw : |(4133481407/10000000000 : ℝ)|=(4133481407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96639221/312500000 : ℝ)|^4609 ≤ (4423300204853/20000000000000 : ℝ)^3585
        have hw : |(96639221/312500000 : ℝ)|=(96639221/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444674779/10000000000 : ℝ)|^4609 ≤ (45767416551871/100000000000000 : ℝ)^3585
        have hw : |(5444674779/10000000000 : ℝ)|=(5444674779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_4 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-821653509/5000000000 : ℝ)*x 0 + (1224781053/2500000000 : ℝ)*x 1 + (1463352263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821653509/5000000000 : ℝ)^4609 ≤ (9810719217199/100000000000000 : ℝ)^3585 := by
    have hnat : (821653509 : ℕ)^4609*100000000000000^3585 ≤ 9810719217199^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821653509 5000000000 9810719217199 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1224781053/2500000000 : ℝ)^4609 ≤ (62434636539/156250000000 : ℝ)^3585 := by
    have hnat : (1224781053 : ℕ)^4609*156250000000^3585 ≤ 62434636539^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224781053 2500000000 62434636539 156250000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1463352263/2500000000 : ℝ)^4609 ≤ (50231113384489/100000000000000 : ℝ)^3585 := by
    have hnat : (1463352263 : ℕ)^4609*100000000000000^3585 ≤ 50231113384489^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463352263 2500000000 50231113384489 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-821653509/5000000000 : ℝ), (1224781053/2500000000 : ℝ), (1463352263/2500000000 : ℝ)] ![(9810719217199/100000000000000 : ℝ), (62434636539/156250000000 : ℝ), (50231113384489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-821653509/5000000000 : ℝ)|^4609 ≤ (9810719217199/100000000000000 : ℝ)^3585
        have hw : |(-821653509/5000000000 : ℝ)|=(821653509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1224781053/2500000000 : ℝ)|^4609 ≤ (62434636539/156250000000 : ℝ)^3585
        have hw : |(1224781053/2500000000 : ℝ)|=(1224781053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1463352263/2500000000 : ℝ)|^4609 ≤ (50231113384489/100000000000000 : ℝ)^3585
        have hw : |(1463352263/2500000000 : ℝ)|=(1463352263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_5 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193467307/10000000000 : ℝ)*x 0 + (-610615417/5000000000 : ℝ)*x 1 + (5853408953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193467307/10000000000 : ℝ)^4609 ≤ (43070726187713/100000000000000 : ℝ)^3585 := by
    have hnat : (5193467307 : ℕ)^4609*100000000000000^3585 ≤ 43070726187713^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193467307 10000000000 43070726187713 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610615417/5000000000 : ℝ)^4609 ≤ (1674540376903/25000000000000 : ℝ)^3585 := by
    have hnat : (610615417 : ℕ)^4609*25000000000000^3585 ≤ 1674540376903^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610615417 5000000000 1674540376903 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5853408953/10000000000 : ℝ)^4609 ≤ (12557778073063/25000000000000 : ℝ)^3585 := by
    have hnat : (5853408953 : ℕ)^4609*25000000000000^3585 ≤ 12557778073063^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5853408953 10000000000 12557778073063 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193467307/10000000000 : ℝ), (-610615417/5000000000 : ℝ), (5853408953/10000000000 : ℝ)] ![(43070726187713/100000000000000 : ℝ), (1674540376903/25000000000000 : ℝ), (12557778073063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193467307/10000000000 : ℝ)|^4609 ≤ (43070726187713/100000000000000 : ℝ)^3585
        have hw : |(5193467307/10000000000 : ℝ)|=(5193467307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610615417/5000000000 : ℝ)|^4609 ≤ (1674540376903/25000000000000 : ℝ)^3585
        have hw : |(-610615417/5000000000 : ℝ)|=(610615417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5853408953/10000000000 : ℝ)|^4609 ≤ (12557778073063/25000000000000 : ℝ)^3585
        have hw : |(5853408953/10000000000 : ℝ)|=(5853408953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_6 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519346723/1000000000 : ℝ)*x 0 + (5853409281/10000000000 : ℝ)*x 1 + (-1221230437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519346723/1000000000 : ℝ)^4609 ≤ (10767681341683/25000000000000 : ℝ)^3585 := by
    have hnat : (519346723 : ℕ)^4609*25000000000000^3585 ≤ 10767681341683^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519346723 1000000000 10767681341683 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5853409281/10000000000 : ℝ)^4609 ≤ (2009244636439/4000000000000 : ℝ)^3585 := by
    have hnat : (5853409281 : ℕ)^4609*4000000000000^3585 ≤ 2009244636439^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5853409281 10000000000 2009244636439 4000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221230437/10000000000 : ℝ)^4609 ≤ (3349079354103/50000000000000 : ℝ)^3585 := by
    have hnat : (1221230437 : ℕ)^4609*50000000000000^3585 ≤ 3349079354103^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221230437 10000000000 3349079354103 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519346723/1000000000 : ℝ), (5853409281/10000000000 : ℝ), (-1221230437/10000000000 : ℝ)] ![(10767681341683/25000000000000 : ℝ), (2009244636439/4000000000000 : ℝ), (3349079354103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519346723/1000000000 : ℝ)|^4609 ≤ (10767681341683/25000000000000 : ℝ)^3585
        have hw : |(519346723/1000000000 : ℝ)|=(519346723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5853409281/10000000000 : ℝ)|^4609 ≤ (2009244636439/4000000000000 : ℝ)^3585
        have hw : |(5853409281/10000000000 : ℝ)|=(5853409281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1221230437/10000000000 : ℝ)|^4609 ≤ (3349079354103/50000000000000 : ℝ)^3585
        have hw : |(-1221230437/10000000000 : ℝ)|=(1221230437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s0_7 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2070436269/5000000000 : ℝ)*x 0 + (2692605621/5000000000 : ℝ)*x 1 + (630806159/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070436269/5000000000 : ℝ)^4609 ≤ (16094965812191/50000000000000 : ℝ)^3585 := by
    have hnat : (2070436269 : ℕ)^4609*50000000000000^3585 ≤ 16094965812191^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070436269 5000000000 16094965812191 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692605621/5000000000 : ℝ)^4609 ≤ (2256290185957/5000000000000 : ℝ)^3585 := by
    have hnat : (2692605621 : ℕ)^4609*5000000000000^3585 ≤ 2256290185957^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692605621 5000000000 2256290185957 5000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630806159/2000000000 : ℝ)^4609 ≤ (22684264640909/100000000000000 : ℝ)^3585 := by
    have hnat : (630806159 : ℕ)^4609*100000000000000^3585 ≤ 22684264640909^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630806159 2000000000 22684264640909 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2070436269/5000000000 : ℝ), (2692605621/5000000000 : ℝ), (630806159/2000000000 : ℝ)] ![(16094965812191/50000000000000 : ℝ), (2256290185957/5000000000000 : ℝ), (22684264640909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2070436269/5000000000 : ℝ)|^4609 ≤ (16094965812191/50000000000000 : ℝ)^3585
        have hw : |(2070436269/5000000000 : ℝ)|=(2070436269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692605621/5000000000 : ℝ)|^4609 ≤ (2256290185957/5000000000000 : ℝ)^3585
        have hw : |(2692605621/5000000000 : ℝ)|=(2692605621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630806159/2000000000 : ℝ)|^4609 ≤ (22684264640909/100000000000000 : ℝ)^3585
        have hw : |(630806159/2000000000 : ℝ)|=(630806159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1556_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24927/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4607/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4607 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4607*1^1024 ≤ 0^1024*1^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4607/1024 : ℝ) ≤ (81026779662592089/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4607 ≤ (81026779662592089/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4607*5000000000000000000^1024 ≤ 81026779662592089^1024*5^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 81026779662592089 5000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (81026779662592089/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4607 := by
      have hnat : (1 : ℕ)^1024*1^4607 ≤ 1^4607*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5081026779662592089/5000000000000000000 : ℝ) ≤ (10035794889162501/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (5081026779662592089/5000000000000000000 : ℝ)^1024 ≤ (10035794889162501/10000000000000000 : ℝ)^4607 := by
      have hnat : (5081026779662592089 : ℕ)^1024*10000000000000000^4607 ≤ 10035794889162501^4607*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5081026779662592089 5000000000000000000 10035794889162501 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035794889162501/10000000000000000 : ℝ)) (X := (5081026779662592089/5000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2581026779662592089/2500000000000000000 : ℝ) ≤ (5035794889162501/5000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (2581026779662592089/2500000000000000000 : ℝ)^1024 ≤ (5035794889162501/5000000000000000 : ℝ)^4607 := by
      have hnat : (2581026779662592089 : ℕ)^1024*5000000000000000^4607 ≤ 5035794889162501^4607*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2581026779662592089 2500000000000000000 5035794889162501 5000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035794889162501/5000000000000000 : ℝ)) (X := (2581026779662592089/2500000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35794889162501/4000000000000000 : ℝ)*(0 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35794889162501/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81026779662592089/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35794889162501/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4607/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35794889162501/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035794889162501/10000000000000000 : ℝ) by norm_num, show 1+(81026779662592089/5000000000000000000 : ℝ)+(0 : ℝ)=(5081026779662592089/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81026779662592089/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35794889162501/4000000000000000 : ℝ)*(2/5 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35794889162501/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035794889162501/5000000000000000 : ℝ) by norm_num, show 1+2*(81026779662592089/5000000000000000000 : ℝ)=(2581026779662592089/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35794889162501/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35794889162501/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35794889162501/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35794889162501/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35794889162501/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35794889162501/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1640145407/10000000000 : ℝ)*X 0 0+(5879745331/10000000000 : ℝ)*X 0 1+(4873691461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2734236413/5000000000 : ℝ)*X 1 0+(-1100474053/5000000000 : ℝ)*X 1 1+(4873691461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2734236433/5000000000 : ℝ)*X 2 0+(974738283/2000000000 : ℝ)*X 2 1+(-137559257/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4133481407/10000000000 : ℝ)*X 0 0+(96639221/312500000 : ℝ)*X 0 1+(5444674779/10000000000 : ℝ)*X 0 2+(4133481407/10000000000 : ℝ)*X 1 0+(96639221/312500000 : ℝ)*X 1 1+(5444674779/10000000000 : ℝ)*X 1 2+(4133481407/10000000000 : ℝ)*X 2 0+(96639221/312500000 : ℝ)*X 2 1+(5444674779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-821653509/5000000000 : ℝ)*X 0 0+(1224781053/2500000000 : ℝ)*X 0 1+(1463352263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5193467307/10000000000 : ℝ)*X 1 0+(-610615417/5000000000 : ℝ)*X 1 1+(5853408953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519346723/1000000000 : ℝ)*X 2 0+(5853409281/10000000000 : ℝ)*X 2 1+(-1221230437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2070436269/5000000000 : ℝ)*X 0 0+(2692605621/5000000000 : ℝ)*X 0 1+(630806159/2000000000 : ℝ)*X 0 2+(2070436269/5000000000 : ℝ)*X 1 0+(2692605621/5000000000 : ℝ)*X 1 1+(630806159/2000000000 : ℝ)*X 1 2+(2070436269/5000000000 : ℝ)*X 2 0+(2692605621/5000000000 : ℝ)*X 2 1+(630806159/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40611540364041918779601/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31645167/100000000000000 : ℝ)*(base1) + (672587921/100000000000000 : ℝ)*(base19) + (21245581/3125000000000 : ℝ)*(base23) + (43238749/50000000000000 : ℝ)*(upper3) + (86741959/100000000000000 : ℝ)*(upper5) + (88694993859867/12500000000000 : ℝ)*(major0) + (88694993859867/12500000000000 : ℝ)*(major1) + (88694993859867/12500000000000 : ℝ)*(major2) + (496992449689083/50000000000000 : ℝ)*(sp0) + (496993337159063/50000000000000 : ℝ)*(sp1) + (198797333409491/20000000000000 : ℝ)*(sp2) + (106282839086009/25000000000000 : ℝ)*(sp3) + (2479173049/100000000000000 : ℝ)*(sp4) + (132320647/12500000000000 : ℝ)*(sp7) + (425132446554379/100000000000000 : ℝ)*(f.failure) + (993987346906047/100000000000000 : ℝ)*(f.sum) + (23423637847367/25000000000000000000000000000 : ℝ)*base65 + (560266240652633/50000000000000000000000000000 : ℝ)*base68 + (374480166652633/50000000000000000000000000000 : ℝ)*base70 + (123638985552633/50000000000000000000000000000 : ℝ)*base72 + (139705260452633/25000000000000000000000000000 : ℝ)*base74 + (108087732747367/50000000000000000000000000000 : ℝ)*base75 + (118219583252633/50000000000000000000000000000 : ℝ)*base78 + (19959084797367/50000000000000000000000000000 : ℝ)*base79 + (88438214852633/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (41364951/10000000000000000000000 : ℝ)*base89 + (41364951/10000000000000000000000 : ℝ)*base91 + (41364951/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40848542546328517532607/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1775820563/100000000000000 : ℝ)*(base19) + (357359019/20000000000000 : ℝ)*(base23) + (1193927/12500000000000 : ℝ)*(base32) + (263548973/100000000000000 : ℝ)*(upper3) + (236486923/100000000000000 : ℝ)*(upper5) + (18701231876123/2500000000000 : ℝ)*(major0) + (18701231876123/2500000000000 : ℝ)*(major1) + (18701231876123/2500000000000 : ℝ)*(major2) + (4720104887/100000000000000 : ℝ)*(sp1) + (1305190811/25000000000000 : ℝ)*(sp2) + (130988121778459/12500000000000 : ℝ)*(sp4) + (523949239151111/50000000000000 : ℝ)*(sp5) + (523948983334667/50000000000000 : ℝ)*(sp6) + (448193293987127/100000000000000 : ℝ)*(sp7) + (224096651769271/50000000000000 : ℝ)*(f.failure) + (130988121778459/12500000000000 : ℝ)*(f.sum) + (7545632286377/5000000000000000000000000000 : ℝ)*base66 + (38776313116377/10000000000000000000000000000 : ℝ)*base68 + (15436180226377/10000000000000000000000000000 : ℝ)*base70 + (13700697443623/10000000000000000000000000000 : ℝ)*base71 + (9996423956377/5000000000000000000000000000 : ℝ)*base74 + (48407945516377/10000000000000000000000000000 : ℝ)*base76 + (73772355636377/10000000000000000000000000000 : ℝ)*base78 + (103060759616377/10000000000000000000000000000 : ℝ)*base80 + (5339140468623/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (36353101/5000000000000000000000 : ℝ)*base90 + (36353101/5000000000000000000000 : ℝ)*base92 + (36353101/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1556_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24927/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1556_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1556_s1_0 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782311197/10000000000 : ℝ)*x 0 + (2771469223/5000000000 : ℝ)*x 1 + (2559466223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782311197/10000000000 : ℝ)^4609 ≤ (5445133477179/50000000000000 : ℝ)^3585 := by
    have hnat : (1782311197 : ℕ)^4609*50000000000000^3585 ≤ 5445133477179^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782311197 10000000000 5445133477179 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771469223/5000000000 : ℝ)^4609 ≤ (2927004360499/6250000000000 : ℝ)^3585 := by
    have hnat : (2771469223 : ℕ)^4609*6250000000000^3585 ≤ 2927004360499^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771469223 5000000000 2927004360499 6250000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559466223/5000000000 : ℝ)^4609 ≤ (21138831631533/50000000000000 : ℝ)^3585 := by
    have hnat : (2559466223 : ℕ)^4609*50000000000000^3585 ≤ 21138831631533^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559466223 5000000000 21138831631533 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782311197/10000000000 : ℝ), (2771469223/5000000000 : ℝ), (2559466223/5000000000 : ℝ)] ![(5445133477179/50000000000000 : ℝ), (2927004360499/6250000000000 : ℝ), (21138831631533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782311197/10000000000 : ℝ)|^4609 ≤ (5445133477179/50000000000000 : ℝ)^3585
        have hw : |(-1782311197/10000000000 : ℝ)|=(1782311197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771469223/5000000000 : ℝ)|^4609 ≤ (2927004360499/6250000000000 : ℝ)^3585
        have hw : |(2771469223/5000000000 : ℝ)|=(2771469223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559466223/5000000000 : ℝ)|^4609 ≤ (21138831631533/50000000000000 : ℝ)^3585
        have hw : |(2559466223/5000000000 : ℝ)|=(2559466223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_1 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689413607/5000000000 : ℝ)*x 0 + (-2004430447/10000000000 : ℝ)*x 1 + (5118932179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689413607/5000000000 : ℝ)^4609 ≤ (45057039742863/100000000000000 : ℝ)^3585 := by
    have hnat : (2689413607 : ℕ)^4609*100000000000000^3585 ≤ 45057039742863^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689413607 5000000000 45057039742863 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004430447/10000000000 : ℝ)^4609 ≤ (12665299813543/100000000000000 : ℝ)^3585 := by
    have hnat : (2004430447 : ℕ)^4609*100000000000000^3585 ≤ 12665299813543^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004430447 10000000000 12665299813543 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5118932179/10000000000 : ℝ)^4609 ≤ (21138830214009/50000000000000 : ℝ)^3585 := by
    have hnat : (5118932179 : ℕ)^4609*50000000000000^3585 ≤ 21138830214009^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118932179 10000000000 21138830214009 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689413607/5000000000 : ℝ), (-2004430447/10000000000 : ℝ), (5118932179/10000000000 : ℝ)] ![(45057039742863/100000000000000 : ℝ), (12665299813543/100000000000000 : ℝ), (21138830214009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689413607/5000000000 : ℝ)|^4609 ≤ (45057039742863/100000000000000 : ℝ)^3585
        have hw : |(2689413607/5000000000 : ℝ)|=(2689413607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004430447/10000000000 : ℝ)|^4609 ≤ (12665299813543/100000000000000 : ℝ)^3585
        have hw : |(-2004430447/10000000000 : ℝ)|=(2004430447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5118932179/10000000000 : ℝ)|^4609 ≤ (21138830214009/50000000000000 : ℝ)^3585
        have hw : |(5118932179/10000000000 : ℝ)|=(5118932179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_2 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215153087/400000000 : ℝ)*x 0 + (1023786411/2000000000 : ℝ)*x 1 + (-2004430661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215153087/400000000 : ℝ)^4609 ≤ (9011407864571/20000000000000 : ℝ)^3585 := by
    have hnat : (215153087 : ℕ)^4609*20000000000000^3585 ≤ 9011407864571^3585*400000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215153087 400000000 9011407864571 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023786411/2000000000 : ℝ)^4609 ≤ (42277659111367/100000000000000 : ℝ)^3585 := by
    have hnat : (1023786411 : ℕ)^4609*100000000000000^3585 ≤ 42277659111367^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023786411 2000000000 42277659111367 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004430661/10000000000 : ℝ)^4609 ≤ (395790673499/3125000000000 : ℝ)^3585 := by
    have hnat : (2004430661 : ℕ)^4609*3125000000000^3585 ≤ 395790673499^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004430661 10000000000 395790673499 3125000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215153087/400000000 : ℝ), (1023786411/2000000000 : ℝ), (-2004430661/10000000000 : ℝ)] ![(9011407864571/20000000000000 : ℝ), (42277659111367/100000000000000 : ℝ), (395790673499/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215153087/400000000 : ℝ)|^4609 ≤ (9011407864571/20000000000000 : ℝ)^3585
        have hw : |(215153087/400000000 : ℝ)|=(215153087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023786411/2000000000 : ℝ)|^4609 ≤ (42277659111367/100000000000000 : ℝ)^3585
        have hw : |(1023786411/2000000000 : ℝ)|=(1023786411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2004430661/10000000000 : ℝ)|^4609 ≤ (395790673499/3125000000000 : ℝ)^3585
        have hw : |(-2004430661/10000000000 : ℝ)|=(2004430661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_3 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116779047/5000000000 : ℝ)*x 0 + (940383271/2500000000 : ℝ)*x 1 + (4752886833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116779047/5000000000 : ℝ)^4609 ≤ (16559595108163/50000000000000 : ℝ)^3585 := by
    have hnat : (2116779047 : ℕ)^4609*50000000000000^3585 ≤ 16559595108163^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116779047 5000000000 16559595108163 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940383271/2500000000 : ℝ)^4609 ≤ (7112371262459/25000000000000 : ℝ)^3585 := by
    have hnat : (940383271 : ℕ)^4609*25000000000000^3585 ≤ 7112371262459^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940383271 2500000000 7112371262459 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4752886833/10000000000 : ℝ)^4609 ≤ (9607831179343/25000000000000 : ℝ)^3585 := by
    have hnat : (4752886833 : ℕ)^4609*25000000000000^3585 ≤ 9607831179343^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752886833 10000000000 9607831179343 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116779047/5000000000 : ℝ), (940383271/2500000000 : ℝ), (4752886833/10000000000 : ℝ)] ![(16559595108163/50000000000000 : ℝ), (7112371262459/25000000000000 : ℝ), (9607831179343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116779047/5000000000 : ℝ)|^4609 ≤ (16559595108163/50000000000000 : ℝ)^3585
        have hw : |(2116779047/5000000000 : ℝ)|=(2116779047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(940383271/2500000000 : ℝ)|^4609 ≤ (7112371262459/25000000000000 : ℝ)^3585
        have hw : |(940383271/2500000000 : ℝ)|=(940383271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4752886833/10000000000 : ℝ)|^4609 ≤ (9607831179343/25000000000000 : ℝ)^3585
        have hw : |(4752886833/10000000000 : ℝ)|=(4752886833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_4 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-891270583/5000000000 : ℝ)*x 0 + (5123390673/10000000000 : ℝ)*x 1 + (553841303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891270583/5000000000 : ℝ)^4609 ≤ (10892073503741/100000000000000 : ℝ)^3585 := by
    have hnat : (891270583 : ℕ)^4609*100000000000000^3585 ≤ 10892073503741^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891270583 5000000000 10892073503741 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5123390673/10000000000 : ℝ)^4609 ≤ (1058125182557/2500000000000 : ℝ)^3585 := by
    have hnat : (5123390673 : ℕ)^4609*2500000000000^3585 ≤ 1058125182557^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123390673 10000000000 1058125182557 2500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553841303/1000000000 : ℝ)^4609 ≤ (46782919181907/100000000000000 : ℝ)^3585 := by
    have hnat : (553841303 : ℕ)^4609*100000000000000^3585 ≤ 46782919181907^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553841303 1000000000 46782919181907 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891270583/5000000000 : ℝ), (5123390673/10000000000 : ℝ), (553841303/1000000000 : ℝ)] ![(10892073503741/100000000000000 : ℝ), (1058125182557/2500000000000 : ℝ), (46782919181907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891270583/5000000000 : ℝ)|^4609 ≤ (10892073503741/100000000000000 : ℝ)^3585
        have hw : |(-891270583/5000000000 : ℝ)|=(891270583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5123390673/10000000000 : ℝ)|^4609 ≤ (1058125182557/2500000000000 : ℝ)^3585
        have hw : |(5123390673/10000000000 : ℝ)|=(5123390673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553841303/1000000000 : ℝ)|^4609 ≤ (46782919181907/100000000000000 : ℝ)^3585
        have hw : |(553841303/1000000000 : ℝ)|=(553841303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_5 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164581079/312500000 : ℝ)*x 0 + (-316990401/2000000000 : ℝ)*x 1 + (110768241/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164581079/312500000 : ℝ)^4609 ≤ (43851977886781/100000000000000 : ℝ)^3585 := by
    have hnat : (164581079 : ℕ)^4609*100000000000000^3585 ≤ 43851977886781^3585*312500000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164581079 312500000 43851977886781 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316990401/2000000000 : ℝ)^4609 ≤ (9365113559421/100000000000000 : ℝ)^3585 := by
    have hnat : (316990401 : ℕ)^4609*100000000000000^3585 ≤ 9365113559421^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316990401 2000000000 9365113559421 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110768241/200000000 : ℝ)^4609 ≤ (46782908539359/100000000000000 : ℝ)^3585 := by
    have hnat : (110768241 : ℕ)^4609*100000000000000^3585 ≤ 46782908539359^3585*200000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110768241 200000000 46782908539359 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164581079/312500000 : ℝ), (-316990401/2000000000 : ℝ), (110768241/200000000 : ℝ)] ![(43851977886781/100000000000000 : ℝ), (9365113559421/100000000000000 : ℝ), (46782908539359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164581079/312500000 : ℝ)|^4609 ≤ (43851977886781/100000000000000 : ℝ)^3585
        have hw : |(164581079/312500000 : ℝ)|=(164581079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316990401/2000000000 : ℝ)|^4609 ≤ (9365113559421/100000000000000 : ℝ)^3585
        have hw : |(-316990401/2000000000 : ℝ)|=(316990401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110768241/200000000 : ℝ)|^4609 ≤ (46782908539359/100000000000000 : ℝ)^3585
        have hw : |(110768241/200000000 : ℝ)|=(110768241/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_6 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633298269/5000000000 : ℝ)*x 0 + (5538411471/10000000000 : ℝ)*x 1 + (-31699/200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633298269/5000000000 : ℝ)^4609 ≤ (21925999701673/50000000000000 : ℝ)^3585 := by
    have hnat : (2633298269 : ℕ)^4609*50000000000000^3585 ≤ 21925999701673^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633298269 5000000000 21925999701673 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5538411471/10000000000 : ℝ)^4609 ≤ (46782902251569/100000000000000 : ℝ)^3585 := by
    have hnat : (5538411471 : ℕ)^4609*100000000000000^3585 ≤ 46782902251569^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538411471 10000000000 46782902251569 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31699/200000 : ℝ)^4609 ≤ (1170637291051/12500000000000 : ℝ)^3585 := by
    have hnat : (31699 : ℕ)^4609*12500000000000^3585 ≤ 1170637291051^3585*200000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31699 200000 1170637291051 12500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633298269/5000000000 : ℝ), (5538411471/10000000000 : ℝ), (-31699/200000 : ℝ)] ![(21925999701673/50000000000000 : ℝ), (46782902251569/100000000000000 : ℝ), (1170637291051/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633298269/5000000000 : ℝ)|^4609 ≤ (21925999701673/50000000000000 : ℝ)^3585
        have hw : |(2633298269/5000000000 : ℝ)|=(2633298269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5538411471/10000000000 : ℝ)|^4609 ≤ (46782902251569/100000000000000 : ℝ)^3585
        have hw : |(5538411471/10000000000 : ℝ)|=(5538411471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31699/200000 : ℝ)|^4609 ≤ (1170637291051/12500000000000 : ℝ)^3585
        have hw : |(-31699/200000 : ℝ)|=(31699/200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s1_7 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4234096421/10000000000 : ℝ)*x 0 + (1185615279/2500000000 : ℝ)*x 1 + (943028663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234096421/10000000000 : ℝ)^4609 ≤ (517571946243/1562500000000 : ℝ)^3585 := by
    have hnat : (4234096421 : ℕ)^4609*1562500000000^3585 ≤ 517571946243^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234096421 10000000000 517571946243 1562500000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185615279/2500000000 : ℝ)^4609 ≤ (19161489067843/50000000000000 : ℝ)^3585 := by
    have hnat : (1185615279 : ℕ)^4609*50000000000000^3585 ≤ 19161489067843^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185615279 2500000000 19161489067843 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943028663/2500000000 : ℝ)^4609 ≤ (2855241729111/10000000000000 : ℝ)^3585 := by
    have hnat : (943028663 : ℕ)^4609*10000000000000^3585 ≤ 2855241729111^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943028663 2500000000 2855241729111 10000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234096421/10000000000 : ℝ), (1185615279/2500000000 : ℝ), (943028663/2500000000 : ℝ)] ![(517571946243/1562500000000 : ℝ), (19161489067843/50000000000000 : ℝ), (2855241729111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234096421/10000000000 : ℝ)|^4609 ≤ (517571946243/1562500000000 : ℝ)^3585
        have hw : |(4234096421/10000000000 : ℝ)|=(4234096421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1185615279/2500000000 : ℝ)|^4609 ≤ (19161489067843/50000000000000 : ℝ)^3585
        have hw : |(1185615279/2500000000 : ℝ)|=(1185615279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943028663/2500000000 : ℝ)|^4609 ≤ (2855241729111/10000000000000 : ℝ)^3585
        have hw : |(943028663/2500000000 : ℝ)|=(943028663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1556_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24927/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8909/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8943/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24927/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24927/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24927/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24927/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24927/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24927/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3377/100000 : ℝ) ^ (4607/1024 : ℝ) ≤ (23978761840027/100000000000000000000 : ℝ) := by
    have hpowers : (3377/100000 : ℝ)^4607 ≤ (23978761840027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3377 : ℕ)^4607*100000000000000000000^1024 ≤ 23978761840027^1024*100000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3377 100000 23978761840027 100000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3377/100000 : ℝ)) (X := (23978761840027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24927/100000 : ℝ) ^ (4607/1024 : ℝ) ≤ (6031901941098431/3125000000000000000 : ℝ) := by
    have hpowers : (24927/100000 : ℝ)^4607 ≤ (6031901941098431/3125000000000000000 : ℝ)^1024 := by
      have hnat : (24927 : ℕ)^4607*3125000000000000000^1024 ≤ 6031901941098431^1024*100000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24927 100000 6031901941098431 3125000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24927/100000 : ℝ)) (X := (6031901941098431/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000023978761840027/50000000000000000000 : ℝ) ≤ (10000001065953877/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (50000023978761840027/50000000000000000000 : ℝ)^1024 ≤ (10000001065953877/10000000000000000 : ℝ)^4607 := by
      have hnat : (50000023978761840027 : ℕ)^1024*10000000000000000^4607 ≤ 10000001065953877^4607*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000023978761840027 50000000000000000000 10000001065953877 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001065953877/10000000000000000 : ℝ)) (X := (50000023978761840027/50000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100193044840876989819/100000000000000000000 : ℝ) ≤ (2000857519830941/2000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (100193044840876989819/100000000000000000000 : ℝ)^1024 ≤ (2000857519830941/2000000000000000 : ℝ)^4607 := by
      have hnat : (100193044840876989819 : ℕ)^1024*2000000000000000^4607 ≤ 2000857519830941^4607*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100193044840876989819 100000000000000000000 2000857519830941 2000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000857519830941/2000000000000000 : ℝ)) (X := (100193044840876989819/100000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1568531901941098431/1562500000000000000 : ℝ) ≤ (10008574132355533/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (1568531901941098431/1562500000000000000 : ℝ)^1024 ≤ (10008574132355533/10000000000000000 : ℝ)^4607 := by
      have hnat : (1568531901941098431 : ℕ)^1024*10000000000000000^4607 ≤ 10008574132355533^4607*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1568531901941098431 1562500000000000000 10008574132355533 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008574132355533/10000000000000000 : ℝ)) (X := (1568531901941098431/1562500000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23978761840027/100000000000000000000 : ℝ) ≤ ((107735535863033828519/107750000000000000000 : ℝ)+2*(1071633300207/538750000000000 : ℝ)*(3377/100000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (107735535863033828519/107750000000000000000 : ℝ)+2*(1071633300207/538750000000000 : ℝ)*(3377/100000 : ℝ)=(10000001065953877/10000000000000000 : ℝ) by norm_num, show 1+2*(23978761840027/100000000000000000000 : ℝ)=(50000023978761840027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6031901941098431/3125000000000000000 : ℝ)+(23978761840027/100000000000000000000 : ℝ) ≤ ((107735535863033828519/107750000000000000000 : ℝ)+(1071633300207/538750000000000 : ℝ)*((24927/100000 : ℝ)+(3377/100000 : ℝ)))^(4607/1024 : ℝ) := by
    rw [show (107735535863033828519/107750000000000000000 : ℝ)+(1071633300207/538750000000000 : ℝ)*((24927/100000 : ℝ)+(3377/100000 : ℝ))=(2000857519830941/2000000000000000 : ℝ) by norm_num, show 1+(6031901941098431/3125000000000000000 : ℝ)+(23978761840027/100000000000000000000 : ℝ)=(100193044840876989819/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6031901941098431/3125000000000000000 : ℝ) ≤ ((107735535863033828519/107750000000000000000 : ℝ)+2*(1071633300207/538750000000000 : ℝ)*(24927/100000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (107735535863033828519/107750000000000000000 : ℝ)+2*(1071633300207/538750000000000 : ℝ)*(24927/100000 : ℝ)=(10008574132355533/10000000000000000 : ℝ) by norm_num, show 1+2*(6031901941098431/3125000000000000000 : ℝ)=(1568531901941098431/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (107735535863033828519/107750000000000000000 : ℝ)*(X 1 0+X 2 0)+(1071633300207/538750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (3377/100000 : ℝ)) (hi := (24927/100000 : ℝ)) (c := (107735535863033828519/107750000000000000000 : ℝ)) (alpha := (1071633300207/538750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (107735535863033828519/107750000000000000000 : ℝ)*(X 0 1+X 2 1)+(1071633300207/538750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (3377/100000 : ℝ)) (hi := (24927/100000 : ℝ)) (c := (107735535863033828519/107750000000000000000 : ℝ)) (alpha := (1071633300207/538750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (107735535863033828519/107750000000000000000 : ℝ)*(X 0 2+X 1 2)+(1071633300207/538750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (3377/100000 : ℝ)) (hi := (24927/100000 : ℝ)) (c := (107735535863033828519/107750000000000000000 : ℝ)) (alpha := (1071633300207/538750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1782311197/10000000000 : ℝ)*X 0 0+(2771469223/5000000000 : ℝ)*X 0 1+(2559466223/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689413607/5000000000 : ℝ)*X 1 0+(-2004430447/10000000000 : ℝ)*X 1 1+(5118932179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((215153087/400000000 : ℝ)*X 2 0+(1023786411/2000000000 : ℝ)*X 2 1+(-2004430661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2116779047/5000000000 : ℝ)*X 0 0+(940383271/2500000000 : ℝ)*X 0 1+(4752886833/10000000000 : ℝ)*X 0 2+(2116779047/5000000000 : ℝ)*X 1 0+(940383271/2500000000 : ℝ)*X 1 1+(4752886833/10000000000 : ℝ)*X 1 2+(2116779047/5000000000 : ℝ)*X 2 0+(940383271/2500000000 : ℝ)*X 2 1+(4752886833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-891270583/5000000000 : ℝ)*X 0 0+(5123390673/10000000000 : ℝ)*X 0 1+(553841303/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164581079/312500000 : ℝ)*X 1 0+(-316990401/2000000000 : ℝ)*X 1 1+(110768241/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633298269/5000000000 : ℝ)*X 2 0+(5538411471/10000000000 : ℝ)*X 2 1+(-31699/200000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4234096421/10000000000 : ℝ)*X 0 0+(1185615279/2500000000 : ℝ)*X 0 1+(943028663/2500000000 : ℝ)*X 0 2+(4234096421/10000000000 : ℝ)*X 1 0+(1185615279/2500000000 : ℝ)*X 1 1+(943028663/2500000000 : ℝ)*X 1 2+(4234096421/10000000000 : ℝ)*X 2 0+(1185615279/2500000000 : ℝ)*X 2 1+(943028663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1704145666973667486042895659/538750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15272079/25000000000000 : ℝ)*(base1) + (378494207/100000000000000 : ℝ)*(base19) + (43668103/12500000000000 : ℝ)*(base23) + (68386051/100000000000000 : ℝ)*(upper3) + (336718205925313/20000000000000 : ℝ)*(major0) + (336718205925313/20000000000000 : ℝ)*(major1) + (336718205925313/20000000000000 : ℝ)*(major2) + (2358458866611541/100000000000000 : ℝ)*(sp0) + (47169179085993/2000000000000 : ℝ)*(sp1) + (294807300747633/12500000000000 : ℝ)*(sp2) + (504360960231163/50000000000000 : ℝ)*(sp3) + (527270631/100000000000000 : ℝ)*(sp4) + (9022937/1562500000000 : ℝ)*(sp6) + (31973519/5000000000000 : ℝ)*(sp7) + (1008722621021021/100000000000000 : ℝ)*(f.failure) + (4606365884363/195312500000 : ℝ)*(f.sum) + (10562022236307/10775000000000000000000000000 : ℝ)*base65 + (10852956522306601447/2155000000000000000000000000000000 : ℝ)*base67 + (12758462863448398553/2155000000000000000000000000000000 : ℝ)*base70 + (3020642832101601447/2155000000000000000000000000000000 : ℝ)*base71 + (797614619529/1346875000000000000000000000 : ℝ)*base73 + (3568342667781601447/2155000000000000000000000000000000 : ℝ)*base75 + (22582366812081601447/2155000000000000000000000000000000 : ℝ)*base77 + (8761663711961601447/2155000000000000000000000000000000 : ℝ)*base79 + (20764145930317/2693750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (22617649/10000000000000000000000 : ℝ)*base89 + (22617649/10000000000000000000000 : ℝ)*base91 + (22617649/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14490647258338796208335089869/1346875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8381081/625000000000 : ℝ)*(base19) + (702412453/25000000000000 : ℝ)*(base23) + (186531441/100000000000000 : ℝ)*(upper3) + (18582917/12500000000000 : ℝ)*(lower4) + (3369869/800000000000 : ℝ)*(upper5) + (860018569182217/50000000000000 : ℝ)*(major0) + (860018569182217/50000000000000 : ℝ)*(major1) + (860018569182217/50000000000000 : ℝ)*(major2) + (2093342457/50000000000000 : ℝ)*(sp1) + (16707169163/100000000000000 : ℝ)*(sp2) + (150594664467339/6250000000000 : ℝ)*(sp4) + (48190182076391/2000000000000 : ℝ)*(sp5) + (2409495114658449/100000000000000 : ℝ)*(sp6) + (515279643313767/50000000000000 : ℝ)*(sp7) + (515279643313767/50000000000000 : ℝ)*(f.failure) + (150594664467339/6250000000000 : ℝ)*(f.sum) + (83478067257787/26937500000000000000000000000 : ℝ)*base66 + (32191907951473953377/5387500000000000000000000000000000 : ℝ)*base68 + (14629623009126046623/5387500000000000000000000000000000 : ℝ)*base69 + (35124828008148953377/5387500000000000000000000000000000 : ℝ)*base72 + (7176244210239/3367187500000000000000000000 : ℝ)*base74 + (2187945195448953377/5387500000000000000000000000000000 : ℝ)*base76 + (2941961523411453377/5387500000000000000000000000000000 : ℝ)*base78 + (3343041972123953377/5387500000000000000000000000000000 : ℝ)*base80 + (161425351753801/53875000000000000000000000000 : ℝ)*base81 + (5004323/5000000000000000000000 : ℝ)*base89 + (5004323/5000000000000000000000 : ℝ)*base91 + (5004323/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1556_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24927/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8943/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1556_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1556_s2_0 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901103271/5000000000 : ℝ)*x 0 + (5445077253/10000000000 : ℝ)*x 1 + (2601923689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901103271/5000000000 : ℝ)^4609 ≤ (11046802868833/100000000000000 : ℝ)^3585 := by
    have hnat : (901103271 : ℕ)^4609*100000000000000^3585 ≤ 11046802868833^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901103271 5000000000 11046802868833 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445077253/10000000000 : ℝ)^4609 ≤ (45771766102773/100000000000000 : ℝ)^3585 := by
    have hnat : (5445077253 : ℕ)^4609*100000000000000^3585 ≤ 45771766102773^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445077253 10000000000 45771766102773 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601923689/5000000000 : ℝ)^4609 ≤ (43181431014123/100000000000000 : ℝ)^3585 := by
    have hnat : (2601923689 : ℕ)^4609*100000000000000^3585 ≤ 43181431014123^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601923689 5000000000 43181431014123 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901103271/5000000000 : ℝ), (5445077253/10000000000 : ℝ), (2601923689/5000000000 : ℝ)] ![(11046802868833/100000000000000 : ℝ), (45771766102773/100000000000000 : ℝ), (43181431014123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901103271/5000000000 : ℝ)|^4609 ≤ (11046802868833/100000000000000 : ℝ)^3585
        have hw : |(-901103271/5000000000 : ℝ)|=(901103271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445077253/10000000000 : ℝ)|^4609 ≤ (45771766102773/100000000000000 : ℝ)^3585
        have hw : |(5445077253/10000000000 : ℝ)|=(5445077253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601923689/5000000000 : ℝ)|^4609 ≤ (43181431014123/100000000000000 : ℝ)^3585
        have hw : |(2601923689/5000000000 : ℝ)|=(2601923689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_1 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676822057/5000000000 : ℝ)*x 0 + (-963049083/5000000000 : ℝ)*x 1 + (2601923731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676822057/5000000000 : ℝ)^4609 ≤ (1399562928897/3125000000000 : ℝ)^3585 := by
    have hnat : (2676822057 : ℕ)^4609*3125000000000^3585 ≤ 1399562928897^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676822057 5000000000 1399562928897 3125000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963049083/5000000000 : ℝ)^4609 ≤ (3008138586409/25000000000000 : ℝ)^3585 := by
    have hnat : (963049083 : ℕ)^4609*25000000000000^3585 ≤ 3008138586409^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963049083 5000000000 3008138586409 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601923731/5000000000 : ℝ)^4609 ≤ (172725727641/400000000000 : ℝ)^3585 := by
    have hnat : (2601923731 : ℕ)^4609*400000000000^3585 ≤ 172725727641^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601923731 5000000000 172725727641 400000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676822057/5000000000 : ℝ), (-963049083/5000000000 : ℝ), (2601923731/5000000000 : ℝ)] ![(1399562928897/3125000000000 : ℝ), (3008138586409/25000000000000 : ℝ), (172725727641/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676822057/5000000000 : ℝ)|^4609 ≤ (1399562928897/3125000000000 : ℝ)^3585
        have hw : |(2676822057/5000000000 : ℝ)|=(2676822057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-963049083/5000000000 : ℝ)|^4609 ≤ (3008138586409/25000000000000 : ℝ)^3585
        have hw : |(-963049083/5000000000 : ℝ)|=(963049083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601923731/5000000000 : ℝ)|^4609 ≤ (172725727641/400000000000 : ℝ)^3585
        have hw : |(2601923731/5000000000 : ℝ)|=(2601923731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_2 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338410889/2500000000 : ℝ)*x 0 + (1300961983/2500000000 : ℝ)*x 1 + (-192609829/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338410889/2500000000 : ℝ)^4609 ≤ (44786007723413/100000000000000 : ℝ)^3585 := by
    have hnat : (1338410889 : ℕ)^4609*100000000000000^3585 ≤ 44786007723413^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338410889 2500000000 44786007723413 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300961983/2500000000 : ℝ)^4609 ≤ (43181436924291/100000000000000 : ℝ)^3585 := by
    have hnat : (1300961983 : ℕ)^4609*100000000000000^3585 ≤ 43181436924291^3585*2500000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300961983 2500000000 43181436924291 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192609829/1000000000 : ℝ)^4609 ≤ (6016277670771/50000000000000 : ℝ)^3585 := by
    have hnat : (192609829 : ℕ)^4609*50000000000000^3585 ≤ 6016277670771^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192609829 1000000000 6016277670771 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338410889/2500000000 : ℝ), (1300961983/2500000000 : ℝ), (-192609829/1000000000 : ℝ)] ![(44786007723413/100000000000000 : ℝ), (43181436924291/100000000000000 : ℝ), (6016277670771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338410889/2500000000 : ℝ)|^4609 ≤ (44786007723413/100000000000000 : ℝ)^3585
        have hw : |(1338410889/2500000000 : ℝ)|=(1338410889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300961983/2500000000 : ℝ)|^4609 ≤ (43181436924291/100000000000000 : ℝ)^3585
        have hw : |(1300961983/2500000000 : ℝ)|=(1300961983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192609829/1000000000 : ℝ)|^4609 ≤ (6016277670771/50000000000000 : ℝ)^3585
        have hw : |(-192609829/1000000000 : ℝ)|=(192609829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_3 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247947021/10000000000 : ℝ)*x 0 + (3973602869/10000000000 : ℝ)*x 1 + (2268805969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247947021/10000000000 : ℝ)^4609 ≤ (3326397760327/10000000000000 : ℝ)^3585 := by
    have hnat : (4247947021 : ℕ)^4609*10000000000000^3585 ≤ 3326397760327^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247947021 10000000000 3326397760327 10000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3973602869/10000000000 : ℝ)^4609 ≤ (6105590522091/20000000000000 : ℝ)^3585 := by
    have hnat : (3973602869 : ℕ)^4609*20000000000000^3585 ≤ 6105590522091^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973602869 10000000000 6105590522091 20000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268805969/5000000000 : ℝ)^4609 ≤ (18104034889329/50000000000000 : ℝ)^3585 := by
    have hnat : (2268805969 : ℕ)^4609*50000000000000^3585 ≤ 18104034889329^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268805969 5000000000 18104034889329 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247947021/10000000000 : ℝ), (3973602869/10000000000 : ℝ), (2268805969/5000000000 : ℝ)] ![(3326397760327/10000000000000 : ℝ), (6105590522091/20000000000000 : ℝ), (18104034889329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247947021/10000000000 : ℝ)|^4609 ≤ (3326397760327/10000000000000 : ℝ)^3585
        have hw : |(4247947021/10000000000 : ℝ)|=(4247947021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3973602869/10000000000 : ℝ)|^4609 ≤ (6105590522091/20000000000000 : ℝ)^3585
        have hw : |(3973602869/10000000000 : ℝ)|=(3973602869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2268805969/5000000000 : ℝ)|^4609 ≤ (18104034889329/50000000000000 : ℝ)^3585
        have hw : |(2268805969/5000000000 : ℝ)|=(2268805969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_4 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360449743/2000000000 : ℝ)*x 0 + (2602649613/5000000000 : ℝ)*x 1 + (544361321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360449743/2000000000 : ℝ)^4609 ≤ (11047135211069/100000000000000 : ℝ)^3585 := by
    have hnat : (360449743 : ℕ)^4609*100000000000000^3585 ≤ 11047135211069^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360449743 2000000000 11047135211069 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602649613/5000000000 : ℝ)^4609 ≤ (21598460098041/50000000000000 : ℝ)^3585 := by
    have hnat : (2602649613 : ℕ)^4609*50000000000000^3585 ≤ 21598460098041^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602649613 5000000000 21598460098041 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544361321/1000000000 : ℝ)^4609 ≤ (4575594457833/10000000000000 : ℝ)^3585 := by
    have hnat : (544361321 : ℕ)^4609*10000000000000^3585 ≤ 4575594457833^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544361321 1000000000 4575594457833 10000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360449743/2000000000 : ℝ), (2602649613/5000000000 : ℝ), (544361321/1000000000 : ℝ)] ![(11047135211069/100000000000000 : ℝ), (21598460098041/50000000000000 : ℝ), (4575594457833/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360449743/2000000000 : ℝ)|^4609 ≤ (11047135211069/100000000000000 : ℝ)^3585
        have hw : |(-360449743/2000000000 : ℝ)|=(360449743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602649613/5000000000 : ℝ)|^4609 ≤ (21598460098041/50000000000000 : ℝ)^3585
        have hw : |(2602649613/5000000000 : ℝ)|=(2602649613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544361321/1000000000 : ℝ)|^4609 ≤ (4575594457833/10000000000000 : ℝ)^3585
        have hw : |(544361321/1000000000 : ℝ)|=(544361321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_5 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057984701/2000000000 : ℝ)*x 0 + (-210791671/1250000000 : ℝ)*x 1 + (5443613091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057984701/2000000000 : ℝ)^4609 ≤ (22050933379121/50000000000000 : ℝ)^3585 := by
    have hnat : (1057984701 : ℕ)^4609*50000000000000^3585 ≤ 22050933379121^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057984701 2000000000 22050933379121 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210791671/1250000000 : ℝ)^4609 ≤ (10142189933281/100000000000000 : ℝ)^3585 := by
    have hnat : (210791671 : ℕ)^4609*100000000000000^3585 ≤ 10142189933281^3585*1250000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210791671 1250000000 10142189933281 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443613091/10000000000 : ℝ)^4609 ≤ (22877971646189/50000000000000 : ℝ)^3585 := by
    have hnat : (5443613091 : ℕ)^4609*50000000000000^3585 ≤ 22877971646189^3585*10000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443613091 10000000000 22877971646189 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057984701/2000000000 : ℝ), (-210791671/1250000000 : ℝ), (5443613091/10000000000 : ℝ)] ![(22050933379121/50000000000000 : ℝ), (10142189933281/100000000000000 : ℝ), (22877971646189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057984701/2000000000 : ℝ)|^4609 ≤ (22050933379121/50000000000000 : ℝ)^3585
        have hw : |(1057984701/2000000000 : ℝ)|=(1057984701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210791671/1250000000 : ℝ)|^4609 ≤ (10142189933281/100000000000000 : ℝ)^3585
        have hw : |(-210791671/1250000000 : ℝ)|=(210791671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443613091/10000000000 : ℝ)|^4609 ≤ (22877971646189/50000000000000 : ℝ)^3585
        have hw : |(5443613091/10000000000 : ℝ)|=(5443613091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_6 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165310081/312500000 : ℝ)*x 0 + (1088723033/2000000000 : ℝ)*x 1 + (-337266347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165310081/312500000 : ℝ)^4609 ≤ (11025464243113/25000000000000 : ℝ)^3585 := by
    have hnat : (165310081 : ℕ)^4609*25000000000000^3585 ≤ 11025464243113^3585*312500000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165310081 312500000 11025464243113 25000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088723033/2000000000 : ℝ)^4609 ≤ (22877982852343/50000000000000 : ℝ)^3585 := by
    have hnat : (1088723033 : ℕ)^4609*50000000000000^3585 ≤ 22877982852343^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088723033 2000000000 22877982852343 50000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337266347/2000000000 : ℝ)^4609 ≤ (253554432663/2500000000000 : ℝ)^3585 := by
    have hnat : (337266347 : ℕ)^4609*2500000000000^3585 ≤ 253554432663^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337266347 2000000000 253554432663 2500000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165310081/312500000 : ℝ), (1088723033/2000000000 : ℝ), (-337266347/2000000000 : ℝ)] ![(11025464243113/25000000000000 : ℝ), (22877982852343/50000000000000 : ℝ), (253554432663/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165310081/312500000 : ℝ)|^4609 ≤ (11025464243113/25000000000000 : ℝ)^3585
        have hw : |(165310081/312500000 : ℝ)|=(165310081/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088723033/2000000000 : ℝ)|^4609 ≤ (22877982852343/50000000000000 : ℝ)^3585
        have hw : |(1088723033/2000000000 : ℝ)|=(1088723033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337266347/2000000000 : ℝ)|^4609 ≤ (253554432663/2500000000000 : ℝ)^3585
        have hw : |(-337266347/2000000000 : ℝ)|=(337266347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1556_s2_7 (p : ℝ) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849609149/2000000000 : ℝ)*x 0 + (453421869/1000000000 : ℝ)*x 1 + (1988512903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849609149/2000000000 : ℝ)^4609 ≤ (33264971489837/100000000000000 : ℝ)^3585 := by
    have hnat : (849609149 : ℕ)^4609*100000000000000^3585 ≤ 33264971489837^3585*2000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849609149 2000000000 33264971489837 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453421869/1000000000 : ℝ)^4609 ≤ (36173262924097/100000000000000 : ℝ)^3585 := by
    have hnat : (453421869 : ℕ)^4609*100000000000000^3585 ≤ 36173262924097^3585*1000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453421869 1000000000 36173262924097 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988512903/5000000000 : ℝ)^4609 ≤ (30561765562409/100000000000000 : ℝ)^3585 := by
    have hnat : (1988512903 : ℕ)^4609*100000000000000^3585 ≤ 30561765562409^3585*5000000000^4609 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988512903 5000000000 30561765562409 100000000000000 4609 3585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4609/1024 : ℝ)) 4609 3585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849609149/2000000000 : ℝ), (453421869/1000000000 : ℝ), (1988512903/5000000000 : ℝ)] ![(33264971489837/100000000000000 : ℝ), (36173262924097/100000000000000 : ℝ), (30561765562409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849609149/2000000000 : ℝ)|^4609 ≤ (33264971489837/100000000000000 : ℝ)^3585
        have hw : |(849609149/2000000000 : ℝ)|=(849609149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453421869/1000000000 : ℝ)|^4609 ≤ (36173262924097/100000000000000 : ℝ)^3585
        have hw : |(453421869/1000000000 : ℝ)|=(453421869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1988512903/5000000000 : ℝ)|^4609 ≤ (30561765562409/100000000000000 : ℝ)^3585
        have hw : |(1988512903/5000000000 : ℝ)|=(1988512903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1556_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5369/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (317/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8943/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8943/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8943/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8943/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8943/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8943/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (8909/100000 : ℝ) ^ (4607/1024 : ℝ) ≤ (1884759204220029/100000000000000000000 : ℝ) := by
    have hpowers : (8909/100000 : ℝ)^4607 ≤ (1884759204220029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8909 : ℕ)^4607*100000000000000000000^1024 ≤ 1884759204220029^1024*100000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8909 100000 1884759204220029 100000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8909/100000 : ℝ)) (X := (1884759204220029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8943/50000 : ℝ) ^ (4607/1024 : ℝ) ≤ (43355029535907523/100000000000000000000 : ℝ) := by
    have hpowers : (8943/50000 : ℝ)^4607 ≤ (43355029535907523/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8943 : ℕ)^4607*100000000000000000000^1024 ≤ 43355029535907523^1024*50000^4607 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8943 50000 43355029535907523 100000000000000000000 4607 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8943/50000 : ℝ)) (X := (43355029535907523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001884759204220029/50000000000000000000 : ℝ) ≤ (1250010473003773/1250000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (50001884759204220029/50000000000000000000 : ℝ)^1024 ≤ (1250010473003773/1250000000000000 : ℝ)^4607 := by
      have hnat : (50001884759204220029 : ℕ)^1024*1250000000000000^4607 ≤ 1250010473003773^4607*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001884759204220029 50000000000000000000 1250010473003773 1250000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250010473003773/1250000000000000 : ℝ)) (X := (50001884759204220029/50000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563206871699064493/1562500000000000000 : ℝ) ≤ (10001005370006299/10000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (1563206871699064493/1562500000000000000 : ℝ)^1024 ≤ (10001005370006299/10000000000000000 : ℝ)^4607 := by
      have hnat : (1563206871699064493 : ℕ)^1024*10000000000000000^4607 ≤ 10001005370006299^4607*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563206871699064493 1562500000000000000 10001005370006299 10000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001005370006299/10000000000000000 : ℝ)) (X := (1563206871699064493/1562500000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043355029535907523/50000000000000000000 : ℝ) ≤ (5000963477991207/5000000000000000 : ℝ) ^ (4607/1024 : ℝ) := by
    have hpowers : (50043355029535907523/50000000000000000000 : ℝ)^1024 ≤ (5000963477991207/5000000000000000 : ℝ)^4607 := by
      have hnat : (50043355029535907523 : ℕ)^1024*5000000000000000^4607 ≤ 5000963477991207^4607*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043355029535907523 50000000000000000000 5000963477991207 5000000000000000 1024 4607 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000963477991207/5000000000000000 : ℝ)) (X := (50043355029535907523/50000000000000000000 : ℝ)) (by norm_num) 4607 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1884759204220029/100000000000000000000 : ℝ) ≤ ((44877165655158272349/44885000000000000000 : ℝ)+2*(184317195223/179540000000000 : ℝ)*(8909/100000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (44877165655158272349/44885000000000000000 : ℝ)+2*(184317195223/179540000000000 : ℝ)*(8909/100000 : ℝ)=(1250010473003773/1250000000000000 : ℝ) by norm_num, show 1+2*(1884759204220029/100000000000000000000 : ℝ)=(50001884759204220029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43355029535907523/100000000000000000000 : ℝ)+(1884759204220029/100000000000000000000 : ℝ) ≤ ((44877165655158272349/44885000000000000000 : ℝ)+(184317195223/179540000000000 : ℝ)*((8943/50000 : ℝ)+(8909/100000 : ℝ)))^(4607/1024 : ℝ) := by
    rw [show (44877165655158272349/44885000000000000000 : ℝ)+(184317195223/179540000000000 : ℝ)*((8943/50000 : ℝ)+(8909/100000 : ℝ))=(10001005370006299/10000000000000000 : ℝ) by norm_num, show 1+(43355029535907523/100000000000000000000 : ℝ)+(1884759204220029/100000000000000000000 : ℝ)=(1563206871699064493/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43355029535907523/100000000000000000000 : ℝ) ≤ ((44877165655158272349/44885000000000000000 : ℝ)+2*(184317195223/179540000000000 : ℝ)*(8943/50000 : ℝ))^(4607/1024 : ℝ) := by
    rw [show (44877165655158272349/44885000000000000000 : ℝ)+2*(184317195223/179540000000000 : ℝ)*(8943/50000 : ℝ)=(5000963477991207/5000000000000000 : ℝ) by norm_num, show 1+2*(43355029535907523/100000000000000000000 : ℝ)=(50043355029535907523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44877165655158272349/44885000000000000000 : ℝ)*(X 1 0+X 2 0)+(184317195223/179540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (8909/100000 : ℝ)) (hi := (8943/50000 : ℝ)) (c := (44877165655158272349/44885000000000000000 : ℝ)) (alpha := (184317195223/179540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44877165655158272349/44885000000000000000 : ℝ)*(X 0 1+X 2 1)+(184317195223/179540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (8909/100000 : ℝ)) (hi := (8943/50000 : ℝ)) (c := (44877165655158272349/44885000000000000000 : ℝ)) (alpha := (184317195223/179540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44877165655158272349/44885000000000000000 : ℝ)*(X 0 2+X 1 2)+(184317195223/179540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4607/1024 : ℝ)) (lo := (8909/100000 : ℝ)) (hi := (8943/50000 : ℝ)) (c := (44877165655158272349/44885000000000000000 : ℝ)) (alpha := (184317195223/179540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-901103271/5000000000 : ℝ)*X 0 0+(5445077253/10000000000 : ℝ)*X 0 1+(2601923689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676822057/5000000000 : ℝ)*X 1 0+(-963049083/5000000000 : ℝ)*X 1 1+(2601923731/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338410889/2500000000 : ℝ)*X 2 0+(1300961983/2500000000 : ℝ)*X 2 1+(-192609829/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4247947021/10000000000 : ℝ)*X 0 0+(3973602869/10000000000 : ℝ)*X 0 1+(2268805969/5000000000 : ℝ)*X 0 2+(4247947021/10000000000 : ℝ)*X 1 0+(3973602869/10000000000 : ℝ)*X 1 1+(2268805969/5000000000 : ℝ)*X 1 2+(4247947021/10000000000 : ℝ)*X 2 0+(3973602869/10000000000 : ℝ)*X 2 1+(2268805969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-360449743/2000000000 : ℝ)*X 0 0+(2602649613/5000000000 : ℝ)*X 0 1+(544361321/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057984701/2000000000 : ℝ)*X 1 0+(-210791671/1250000000 : ℝ)*X 1 1+(5443613091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165310081/312500000 : ℝ)*X 2 0+(1088723033/2000000000 : ℝ)*X 2 1+(-337266347/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849609149/2000000000 : ℝ)*X 0 0+(453421869/1000000000 : ℝ)*X 0 1+(1988512903/5000000000 : ℝ)*X 0 2+(849609149/2000000000 : ℝ)*X 1 0+(453421869/1000000000 : ℝ)*X 1 1+(1988512903/5000000000 : ℝ)*X 1 2+(849609149/2000000000 : ℝ)*X 2 0+(453421869/1000000000 : ℝ)*X 2 1+(1988512903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1556_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11336562002457917807387702481/1122125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352074169/25000000000000 : ℝ)*(base19) + (830990563/100000000000000 : ℝ)*(base23) + (197964357/100000000000000 : ℝ)*(lower2) + (57899889/20000000000000 : ℝ)*(upper3) + (60106111/50000000000000 : ℝ)*(lower4) + (1479625117758223/50000000000000 : ℝ)*(major0) + (1479625117758223/50000000000000 : ℝ)*(major1) + (1479625117758223/50000000000000 : ℝ)*(major2) + (2072724733342999/50000000000000 : ℝ)*(sp0) + (4145465607305333/100000000000000 : ℝ)*(sp1) + (2072733092305723/50000000000000 : ℝ)*(sp2) + (1773025958876511/100000000000000 : ℝ)*(sp3) + (17548916011/100000000000000 : ℝ)*(sp4) + (3579897813/50000000000000 : ℝ)*(sp7) + (1773033118672137/100000000000000 : ℝ)*(f.failure) + (414546701560201/10000000000000 : ℝ)*(f.sum) + (22300987527591/4488500000000000000000000000 : ℝ)*base66 + (11772391066870224173/2244250000000000000000000000000000 : ℝ)*base68 + (12218505770461525827/2244250000000000000000000000000000 : ℝ)*base69 + (7920638842387224173/2244250000000000000000000000000000 : ℝ)*base72 + (5437841214959/8977000000000000000000000000 : ℝ)*base74 + (5936121857859474173/2244250000000000000000000000000000 : ℝ)*base76 + (8180773147693275827/2244250000000000000000000000000000 : ℝ)*base77 + (1201791091391224173/2244250000000000000000000000000000 : ℝ)*base80 + (988548394937/448850000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4515853/10000000000000000000000 : ℝ)*base89 + (4515853/10000000000000000000000 : ℝ)*base91 + (4515853/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (820512682881518100699736851/561062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156519639/50000000000000 : ℝ)*(base8) + (181231771/50000000000000 : ℝ)*(base21) + (245090679/100000000000000 : ℝ)*(base29) + (34477529/100000000000000 : ℝ)*(lower4) + (94263313/100000000000000 : ℝ)*(upper5) + (1497714985309263/50000000000000 : ℝ)*(major0) + (1497715107854603/50000000000000 : ℝ)*(major1) + (1497715107854603/50000000000000 : ℝ)*(major2) + (529432469/100000000000000 : ℝ)*(sp0) + (3489978079/12500000000000 : ℝ)*(sp2) + (4196149206688979/100000000000000 : ℝ)*(sp4) + (131129681377189/3125000000000 : ℝ)*(sp5) + (2098060760890937/50000000000000 : ℝ)*(sp6) + (112169395844383/6250000000000 : ℝ)*(sp7) + (112169395844383/6250000000000 : ℝ)*(f.failure) + (4196150049160727/100000000000000 : ℝ)*(f.sum) + (14440627502991/8977000000000000000000000000 : ℝ)*base66 + (6529679689187227553/2244250000000000000000000000000000 : ℝ)*base68 + (14549793455964522447/2244250000000000000000000000000000 : ℝ)*base69 + (24580763616386281213/2244250000000000000000000000000000 : ℝ)*base72 + (19834365743397/4488500000000000000000000000 : ℝ)*base74 + (605233088138477553/2244250000000000000000000000000000 : ℝ)*base76 + (23557140005666281213/2244250000000000000000000000000000 : ℝ)*base78 + (7113133965284977553/2244250000000000000000000000000000 : ℝ)*base80 + (363318279393/2244250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6738027/625000000000000000000 : ℝ)*base89 + (488027/625000000000000000000 : ℝ)*base91 + (488027/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1556_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (317/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1556_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1556_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (317/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1556_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1556_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1556_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4607/1024 : ℝ) ≤ p) (hpb : p ≤ (4609/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166903269/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (317/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1556_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
