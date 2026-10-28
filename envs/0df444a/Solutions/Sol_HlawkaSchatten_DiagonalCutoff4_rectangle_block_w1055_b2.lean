-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1055_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:58:39.78777+00:00
-- url     : https://prove2.me/submissions/8806fc72-3c75-4a40-8bf7-81556628e659

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
theorem support_rectangle_w1055_s6_0 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209143579/10000000000 : ℝ)*x 0 + (21074767/39062500 : ℝ)*x 1 + (5263691709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209143579/10000000000 : ℝ)^1031 ≤ (104808458559/781250000000 : ℝ)^775 := by
    have hnat : (2209143579 : ℕ)^1031*781250000000^775 ≤ 104808458559^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209143579 10000000000 104808458559 781250000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21074767/39062500 : ℝ)^1031 ≤ (44002484938597/100000000000000 : ℝ)^775 := by
    have hnat : (21074767 : ℕ)^1031*100000000000000^775 ≤ 44002484938597^775*39062500^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21074767 39062500 44002484938597 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263691709/10000000000 : ℝ)^1031 ≤ (42582032349861/100000000000000 : ℝ)^775 := by
    have hnat : (5263691709 : ℕ)^1031*100000000000000^775 ≤ 42582032349861^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263691709 10000000000 42582032349861 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209143579/10000000000 : ℝ), (21074767/39062500 : ℝ), (5263691709/10000000000 : ℝ)] ![(104808458559/781250000000 : ℝ), (44002484938597/100000000000000 : ℝ), (42582032349861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209143579/10000000000 : ℝ)|^1031 ≤ (104808458559/781250000000 : ℝ)^775
        have hw : |(-2209143579/10000000000 : ℝ)|=(2209143579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21074767/39062500 : ℝ)|^1031 ≤ (44002484938597/100000000000000 : ℝ)^775
        have hw : |(21074767/39062500 : ℝ)|=(21074767/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263691709/10000000000 : ℝ)|^1031 ≤ (42582032349861/100000000000000 : ℝ)^775
        have hw : |(5263691709/10000000000 : ℝ)|=(5263691709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_1 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (83517989/156250000 : ℝ)*x 0 + (-1137923979/5000000000 : ℝ)*x 1 + (131592293/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83517989/156250000 : ℝ)^1031 ≤ (21730466661211/50000000000000 : ℝ)^775 := by
    have hnat : (83517989 : ℕ)^1031*50000000000000^775 ≤ 21730466661211^775*156250000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83517989 156250000 21730466661211 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137923979/5000000000 : ℝ)^1031 ≤ (6978517097959/50000000000000 : ℝ)^775 := by
    have hnat : (1137923979 : ℕ)^1031*50000000000000^775 ≤ 6978517097959^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137923979 5000000000 6978517097959 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131592293/250000000 : ℝ)^1031 ≤ (42582032468243/100000000000000 : ℝ)^775 := by
    have hnat : (131592293 : ℕ)^1031*100000000000000^775 ≤ 42582032468243^775*250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131592293 250000000 42582032468243 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83517989/156250000 : ℝ), (-1137923979/5000000000 : ℝ), (131592293/250000000 : ℝ)] ![(21730466661211/50000000000000 : ℝ), (6978517097959/50000000000000 : ℝ), (42582032468243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83517989/156250000 : ℝ)|^1031 ≤ (21730466661211/50000000000000 : ℝ)^775
        have hw : |(83517989/156250000 : ℝ)|=(83517989/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1137923979/5000000000 : ℝ)|^1031 ≤ (6978517097959/50000000000000 : ℝ)^775
        have hw : |(-1137923979/5000000000 : ℝ)|=(1137923979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131592293/250000000 : ℝ)|^1031 ≤ (42582032468243/100000000000000 : ℝ)^775
        have hw : |(131592293/250000000 : ℝ)|=(131592293/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_2 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345151153/10000000000 : ℝ)*x 0 + (5263691809/10000000000 : ℝ)*x 1 + (-227584803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345151153/10000000000 : ℝ)^1031 ≤ (43460931775629/100000000000000 : ℝ)^775 := by
    have hnat : (5345151153 : ℕ)^1031*100000000000000^775 ≤ 43460931775629^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345151153 10000000000 43460931775629 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263691809/10000000000 : ℝ)^1031 ≤ (42582033426061/100000000000000 : ℝ)^775 := by
    have hnat : (5263691809 : ℕ)^1031*100000000000000^775 ≤ 42582033426061^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263691809 10000000000 42582033426061 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227584803/1000000000 : ℝ)^1031 ≤ (558281391333/4000000000000 : ℝ)^775 := by
    have hnat : (227584803 : ℕ)^1031*4000000000000^775 ≤ 558281391333^775*1000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227584803 1000000000 558281391333 4000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345151153/10000000000 : ℝ), (5263691809/10000000000 : ℝ), (-227584803/1000000000 : ℝ)] ![(43460931775629/100000000000000 : ℝ), (42582033426061/100000000000000 : ℝ), (558281391333/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345151153/10000000000 : ℝ)|^1031 ≤ (43460931775629/100000000000000 : ℝ)^775
        have hw : |(5345151153/10000000000 : ℝ)|=(5345151153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263691809/10000000000 : ℝ)|^1031 ≤ (42582033426061/100000000000000 : ℝ)^775
        have hw : |(5263691809/10000000000 : ℝ)|=(5263691809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-227584803/1000000000 : ℝ)|^1031 ≤ (558281391333/4000000000000 : ℝ)^775
        have hw : |(-227584803/1000000000 : ℝ)|=(227584803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_3 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (218852357/500000000 : ℝ)*x 0 + (85008691/200000000 : ℝ)*x 1 + (35214791/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218852357/500000000 : ℝ)^1031 ≤ (3331618613647/10000000000000 : ℝ)^775 := by
    have hnat : (218852357 : ℕ)^1031*10000000000000^775 ≤ 3331618613647^775*500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218852357 500000000 3331618613647 10000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85008691/200000000 : ℝ)^1031 ≤ (16020146274531/50000000000000 : ℝ)^775 := by
    have hnat : (85008691 : ℕ)^1031*50000000000000^775 ≤ 16020146274531^775*200000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85008691 200000000 16020146274531 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35214791/78125000 : ℝ)^1031 ≤ (17321760652281/50000000000000 : ℝ)^775 := by
    have hnat : (35214791 : ℕ)^1031*50000000000000^775 ≤ 17321760652281^775*78125000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35214791 78125000 17321760652281 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218852357/500000000 : ℝ), (85008691/200000000 : ℝ), (35214791/78125000 : ℝ)] ![(3331618613647/10000000000000 : ℝ), (16020146274531/50000000000000 : ℝ), (17321760652281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218852357/500000000 : ℝ)|^1031 ≤ (3331618613647/10000000000000 : ℝ)^775
        have hw : |(218852357/500000000 : ℝ)|=(218852357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85008691/200000000 : ℝ)|^1031 ≤ (16020146274531/50000000000000 : ℝ)^775
        have hw : |(85008691/200000000 : ℝ)|=(85008691/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35214791/78125000 : ℝ)|^1031 ≤ (17321760652281/50000000000000 : ℝ)^775
        have hw : |(35214791/78125000 : ℝ)|=(35214791/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_4 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-552287203/2500000000 : ℝ)*x 0 + (2632011879/5000000000 : ℝ)*x 1 + (1078961419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552287203/2500000000 : ℝ)^1031 ≤ (3353881242799/25000000000000 : ℝ)^775 := by
    have hnat : (552287203 : ℕ)^1031*25000000000000^775 ≤ 3353881242799^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552287203 2500000000 3353881242799 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632011879/5000000000 : ℝ)^1031 ≤ (5323200737217/12500000000000 : ℝ)^775 := by
    have hnat : (2632011879 : ℕ)^1031*12500000000000^775 ≤ 5323200737217^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632011879 5000000000 5323200737217 12500000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078961419/2000000000 : ℝ)^1031 ≤ (8799773824609/20000000000000 : ℝ)^775 := by
    have hnat : (1078961419 : ℕ)^1031*20000000000000^775 ≤ 8799773824609^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078961419 2000000000 8799773824609 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552287203/2500000000 : ℝ), (2632011879/5000000000 : ℝ), (1078961419/2000000000 : ℝ)] ![(3353881242799/25000000000000 : ℝ), (5323200737217/12500000000000 : ℝ), (8799773824609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552287203/2500000000 : ℝ)|^1031 ≤ (3353881242799/25000000000000 : ℝ)^775
        have hw : |(-552287203/2500000000 : ℝ)|=(552287203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632011879/5000000000 : ℝ)|^1031 ≤ (5323200737217/12500000000000 : ℝ)^775
        have hw : |(2632011879/5000000000 : ℝ)|=(2632011879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078961419/2000000000 : ℝ)|^1031 ≤ (8799773824609/20000000000000 : ℝ)^775
        have hw : |(1078961419/2000000000 : ℝ)|=(1078961419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_5 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312071071/10000000000 : ℝ)*x 0 + (-2144732583/10000000000 : ℝ)*x 1 + (134870179/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312071071/10000000000 : ℝ)^1031 ≤ (10775869924531/25000000000000 : ℝ)^775 := by
    have hnat : (5312071071 : ℕ)^1031*25000000000000^775 ≤ 10775869924531^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312071071 10000000000 10775869924531 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144732583/10000000000 : ℝ)^1031 ≤ (12897650462297/100000000000000 : ℝ)^775 := by
    have hnat : (2144732583 : ℕ)^1031*100000000000000^775 ≤ 12897650462297^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144732583 10000000000 12897650462297 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134870179/250000000 : ℝ)^1031 ≤ (10999717457071/25000000000000 : ℝ)^775 := by
    have hnat : (134870179 : ℕ)^1031*25000000000000^775 ≤ 10999717457071^775*250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134870179 250000000 10999717457071 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312071071/10000000000 : ℝ), (-2144732583/10000000000 : ℝ), (134870179/250000000 : ℝ)] ![(10775869924531/25000000000000 : ℝ), (12897650462297/100000000000000 : ℝ), (10999717457071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312071071/10000000000 : ℝ)|^1031 ≤ (10775869924531/25000000000000 : ℝ)^775
        have hw : |(5312071071/10000000000 : ℝ)|=(5312071071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144732583/10000000000 : ℝ)|^1031 ≤ (12897650462297/100000000000000 : ℝ)^775
        have hw : |(-2144732583/10000000000 : ℝ)|=(2144732583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134870179/250000000 : ℝ)|^1031 ≤ (10999717457071/25000000000000 : ℝ)^775
        have hw : |(134870179/250000000 : ℝ)|=(134870179/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_6 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328017743/2500000000 : ℝ)*x 0 + (215792291/400000000 : ℝ)*x 1 + (-2144732559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328017743/2500000000 : ℝ)^1031 ≤ (43103478629461/100000000000000 : ℝ)^775 := by
    have hnat : (1328017743 : ℕ)^1031*100000000000000^775 ≤ 43103478629461^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328017743 2500000000 43103478629461 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215792291/400000000 : ℝ)^1031 ≤ (43998871076013/100000000000000 : ℝ)^775 := by
    have hnat : (215792291 : ℕ)^1031*100000000000000^775 ≤ 43998871076013^775*400000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215792291 400000000 43998871076013 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144732559/10000000000 : ℝ)^1031 ≤ (2579530054059/20000000000000 : ℝ)^775 := by
    have hnat : (2144732559 : ℕ)^1031*20000000000000^775 ≤ 2579530054059^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144732559 10000000000 2579530054059 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328017743/2500000000 : ℝ), (215792291/400000000 : ℝ), (-2144732559/10000000000 : ℝ)] ![(43103478629461/100000000000000 : ℝ), (43998871076013/100000000000000 : ℝ), (2579530054059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328017743/2500000000 : ℝ)|^1031 ≤ (43103478629461/100000000000000 : ℝ)^775
        have hw : |(1328017743/2500000000 : ℝ)|=(1328017743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215792291/400000000 : ℝ)|^1031 ≤ (43998871076013/100000000000000 : ℝ)^775
        have hw : |(215792291/400000000 : ℝ)|=(215792291/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144732559/10000000000 : ℝ)|^1031 ≤ (2579530054059/20000000000000 : ℝ)^775
        have hw : |(-2144732559/10000000000 : ℝ)|=(2144732559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s6_7 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4377057427/10000000000 : ℝ)*x 0 + (2253421937/5000000000 : ℝ)*x 1 + (4251086223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377057427/10000000000 : ℝ)^1031 ≤ (33316290301017/100000000000000 : ℝ)^775 := by
    have hnat : (4377057427 : ℕ)^1031*100000000000000^775 ≤ 33316290301017^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377057427 10000000000 33316290301017 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253421937/5000000000 : ℝ)^1031 ≤ (270600639923/781250000000 : ℝ)^775 := by
    have hnat : (2253421937 : ℕ)^1031*781250000000^775 ≤ 270600639923^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253421937 5000000000 270600639923 781250000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251086223/10000000000 : ℝ)^1031 ≤ (8011706944579/25000000000000 : ℝ)^775 := by
    have hnat : (4251086223 : ℕ)^1031*25000000000000^775 ≤ 8011706944579^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251086223 10000000000 8011706944579 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377057427/10000000000 : ℝ), (2253421937/5000000000 : ℝ), (4251086223/10000000000 : ℝ)] ![(33316290301017/100000000000000 : ℝ), (270600639923/781250000000 : ℝ), (8011706944579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377057427/10000000000 : ℝ)|^1031 ≤ (33316290301017/100000000000000 : ℝ)^775
        have hw : |(4377057427/10000000000 : ℝ)|=(4377057427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253421937/5000000000 : ℝ)|^1031 ≤ (270600639923/781250000000 : ℝ)^775
        have hw : |(2253421937/5000000000 : ℝ)|=(2253421937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251086223/10000000000 : ℝ)|^1031 ≤ (8011706944579/25000000000000 : ℝ)^775
        have hw : |(4251086223/10000000000 : ℝ)|=(4251086223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1055_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1403/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7027/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7027/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11181/100000 : ℝ) ^ (8247/2048 : ℝ) ≤ (14735643010753621/100000000000000000000 : ℝ) := by
    have hpowers : (11181/100000 : ℝ)^8247 ≤ (14735643010753621/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11181 : ℕ)^8247*100000000000000000000^2048 ≤ 14735643010753621^2048*100000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11181 100000 14735643010753621 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11181/100000 : ℝ)) (X := (14735643010753621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7027/50000 : ℝ) ^ (8247/2048 : ℝ) ≤ (37009529585401139/100000000000000000000 : ℝ) := by
    have hpowers : (7027/50000 : ℝ)^8247 ≤ (37009529585401139/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7027 : ℕ)^8247*100000000000000000000^2048 ≤ 37009529585401139^2048*50000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7027 50000 37009529585401139 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7027/50000 : ℝ)) (X := (37009529585401139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014735643010753621/50000000000000000000 : ℝ) ≤ (500036589371637/500000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50014735643010753621/50000000000000000000 : ℝ)^2048 ≤ (500036589371637/500000000000000 : ℝ)^8247 := by
      have hnat : (50014735643010753621 : ℕ)^2048*500000000000000^8247 ≤ 500036589371637^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014735643010753621 50000000000000000000 500036589371637 500000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500036589371637/500000000000000 : ℝ)) (X := (50014735643010753621/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501293629314903869/2500000000000000000 : ℝ) ≤ (2000256950431199/2000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (2501293629314903869/2500000000000000000 : ℝ)^2048 ≤ (2000256950431199/2000000000000000 : ℝ)^8247 := by
      have hnat : (2501293629314903869 : ℕ)^2048*2000000000000000^8247 ≤ 2000256950431199^8247*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501293629314903869 2500000000000000000 2000256950431199 2000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000256950431199/2000000000000000 : ℝ)) (X := (2501293629314903869/2500000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037009529585401139/50000000000000000000 : ℝ) ≤ (40007350867517/40000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50037009529585401139/50000000000000000000 : ℝ)^2048 ≤ (40007350867517/40000000000000 : ℝ)^8247 := by
      have hnat : (50037009529585401139 : ℕ)^2048*40000000000000^8247 ≤ 40007350867517^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037009529585401139 50000000000000000000 40007350867517 40000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40007350867517/40000000000000 : ℝ)) (X := (50037009529585401139/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14735643010753621/100000000000000000000 : ℝ) ≤ ((2871973702815283371/2873000000000000000 : ℝ)+2*(110592944651/57460000000000 : ℝ)*(11181/100000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (2871973702815283371/2873000000000000000 : ℝ)+2*(110592944651/57460000000000 : ℝ)*(11181/100000 : ℝ)=(500036589371637/500000000000000 : ℝ) by norm_num, show 1+2*(14735643010753621/100000000000000000000 : ℝ)=(50014735643010753621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37009529585401139/100000000000000000000 : ℝ)+(14735643010753621/100000000000000000000 : ℝ) ≤ ((2871973702815283371/2873000000000000000 : ℝ)+(110592944651/57460000000000 : ℝ)*((7027/50000 : ℝ)+(11181/100000 : ℝ)))^(8247/2048 : ℝ) := by
    rw [show (2871973702815283371/2873000000000000000 : ℝ)+(110592944651/57460000000000 : ℝ)*((7027/50000 : ℝ)+(11181/100000 : ℝ))=(2000256950431199/2000000000000000 : ℝ) by norm_num, show 1+(37009529585401139/100000000000000000000 : ℝ)+(14735643010753621/100000000000000000000 : ℝ)=(2501293629314903869/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37009529585401139/100000000000000000000 : ℝ) ≤ ((2871973702815283371/2873000000000000000 : ℝ)+2*(110592944651/57460000000000 : ℝ)*(7027/50000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (2871973702815283371/2873000000000000000 : ℝ)+2*(110592944651/57460000000000 : ℝ)*(7027/50000 : ℝ)=(40007350867517/40000000000000 : ℝ) by norm_num, show 1+2*(37009529585401139/100000000000000000000 : ℝ)=(50037009529585401139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2871973702815283371/2873000000000000000 : ℝ)*(X 1 0+X 2 0)+(110592944651/57460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (2871973702815283371/2873000000000000000 : ℝ)) (alpha := (110592944651/57460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2871973702815283371/2873000000000000000 : ℝ)*(X 0 1+X 2 1)+(110592944651/57460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (2871973702815283371/2873000000000000000 : ℝ)) (alpha := (110592944651/57460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2871973702815283371/2873000000000000000 : ℝ)*(X 0 2+X 1 2)+(110592944651/57460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (7027/50000 : ℝ)) (c := (2871973702815283371/2873000000000000000 : ℝ)) (alpha := (110592944651/57460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209143579/10000000000 : ℝ)*X 0 0+(21074767/39062500 : ℝ)*X 0 1+(5263691709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83517989/156250000 : ℝ)*X 1 0+(-1137923979/5000000000 : ℝ)*X 1 1+(131592293/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345151153/10000000000 : ℝ)*X 2 0+(5263691809/10000000000 : ℝ)*X 2 1+(-227584803/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218852357/500000000 : ℝ)*X 0 0+(85008691/200000000 : ℝ)*X 0 1+(35214791/78125000 : ℝ)*X 0 2+(218852357/500000000 : ℝ)*X 1 0+(85008691/200000000 : ℝ)*X 1 1+(35214791/78125000 : ℝ)*X 1 2+(218852357/500000000 : ℝ)*X 2 0+(85008691/200000000 : ℝ)*X 2 1+(35214791/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-552287203/2500000000 : ℝ)*X 0 0+(2632011879/5000000000 : ℝ)*X 0 1+(1078961419/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312071071/10000000000 : ℝ)*X 1 0+(-2144732583/10000000000 : ℝ)*X 1 1+(134870179/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328017743/2500000000 : ℝ)*X 2 0+(215792291/400000000 : ℝ)*X 2 1+(-2144732559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377057427/10000000000 : ℝ)*X 0 0+(2253421937/5000000000 : ℝ)*X 0 1+(4251086223/10000000000 : ℝ)*X 0 2+(4377057427/10000000000 : ℝ)*X 1 0+(2253421937/5000000000 : ℝ)*X 1 1+(4251086223/10000000000 : ℝ)*X 1 2+(4377057427/10000000000 : ℝ)*X 2 0+(2253421937/5000000000 : ℝ)*X 2 1+(4251086223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619890847893879153181738743/71825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922860597/50000000000000 : ℝ)*(base19) + (786503851/50000000000000 : ℝ)*(base23) + (36980341/100000000000000 : ℝ)*(lower2) + (293632571/100000000000000 : ℝ)*(upper3) + (90989967/100000000000000 : ℝ)*(upper5) + (5748924809037489/100000000000000 : ℝ)*(major0) + (5748924809037489/100000000000000 : ℝ)*(major1) + (5748924809037489/100000000000000 : ℝ)*(major2) + (1901897317795983/25000000000000 : ℝ)*(sp0) + (7607632342104613/100000000000000 : ℝ)*(sp1) + (950954076852263/12500000000000 : ℝ)*(sp2) + (1945093436095389/50000000000000 : ℝ)*(sp3) + (22458320937/50000000000000 : ℝ)*(sp4) + (7067593161/25000000000000 : ℝ)*(sp7) + (3890215142563423/100000000000000 : ℝ)*(f.failure) + (3803817093912903/50000000000000 : ℝ)*(f.sum) + (1301369254477/2873000000000000000000000000 : ℝ)*base66 + (5005412413026645419/287300000000000000000000000000000 : ℝ)*base67 + (949731315114045419/287300000000000000000000000000000 : ℝ)*base69 + (2293041543085445419/287300000000000000000000000000000 : ℝ)*base71 + (14161240543093/2873000000000000000000000000 : ℝ)*base73 + (1322865853002554581/287300000000000000000000000000000 : ℝ)*base76 + (3460529491278245419/287300000000000000000000000000000 : ℝ)*base77 + (5180997652492645419/287300000000000000000000000000000 : ℝ)*base79 + (3824522873711/2873000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (16169031/10000000000000000000000 : ℝ)*base89 + (16169031/10000000000000000000000 : ℝ)*base91 + (16169031/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (794968267978717552542848523/71825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2126704943/100000000000000 : ℝ)*(base19) + (2163488907/100000000000000 : ℝ)*(base23) + (136745351/50000000000000 : ℝ)*(upper3) + (118257/156250000000 : ℝ)*(lower4) + (235846971/100000000000000 : ℝ)*(upper5) + (2889045084247857/50000000000000 : ℝ)*(major0) + (2889045084247857/50000000000000 : ℝ)*(major1) + (2889045084247857/50000000000000 : ℝ)*(major2) + (1440712139/2500000000000 : ℝ)*(sp1) + (63539372827/100000000000000 : ℝ)*(sp2) + (7646229044144943/100000000000000 : ℝ)*(sp4) + (7646169288954439/100000000000000 : ℝ)*(sp5) + (7646163341283209/100000000000000 : ℝ)*(sp6) + (390995092390889/10000000000000 : ℝ)*(sp7) + (390995092390889/10000000000000 : ℝ)*(f.failure) + (7646229044144943/100000000000000 : ℝ)*(f.sum) + (257561739923/718250000000000000000000000 : ℝ)*base65 + (541597881697264053/143650000000000000000000000000000 : ℝ)*base68 + (1281136438350914053/143650000000000000000000000000000 : ℝ)*base70 + (894782998010514053/143650000000000000000000000000000 : ℝ)*base72 + (399208762483/114920000000000000000000000 : ℝ)*base73 + (999262939921664053/143650000000000000000000000000000 : ℝ)*base76 + (621217194948014053/143650000000000000000000000000000 : ℝ)*base78 + (2190421735649864053/143650000000000000000000000000000 : ℝ)*base80 + (6262349097097/2873000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7447233/1000000000000000000000 : ℝ)*base89 + (7447233/1000000000000000000000 : ℝ)*base91 + (7447233/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1055_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1055_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1055_s7_0 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-44183717/200000000 : ℝ)*x 0 + (1078931609/2000000000 : ℝ)*x 1 + (5264146217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44183717/200000000 : ℝ)^1031 ≤ (6707912094831/50000000000000 : ℝ)^775 := by
    have hnat : (44183717 : ℕ)^1031*50000000000000^775 ≤ 6707912094831^775*200000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44183717 200000000 6707912094831 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078931609/2000000000 : ℝ)^1031 ≤ (8799450392933/20000000000000 : ℝ)^775 := by
    have hnat : (1078931609 : ℕ)^1031*20000000000000^775 ≤ 8799450392933^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078931609 2000000000 8799450392933 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264146217/10000000000 : ℝ)^1031 ≤ (10646730958441/25000000000000 : ℝ)^775 := by
    have hnat : (5264146217 : ℕ)^1031*25000000000000^775 ≤ 10646730958441^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264146217 10000000000 10646730958441 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44183717/200000000 : ℝ), (1078931609/2000000000 : ℝ), (5264146217/10000000000 : ℝ)] ![(6707912094831/50000000000000 : ℝ), (8799450392933/20000000000000 : ℝ), (10646730958441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44183717/200000000 : ℝ)|^1031 ≤ (6707912094831/50000000000000 : ℝ)^775
        have hw : |(-44183717/200000000 : ℝ)|=(44183717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078931609/2000000000 : ℝ)|^1031 ≤ (8799450392933/20000000000000 : ℝ)^775
        have hw : |(1078931609/2000000000 : ℝ)|=(1078931609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264146217/10000000000 : ℝ)|^1031 ≤ (10646730958441/25000000000000 : ℝ)^775
        have hw : |(5264146217/10000000000 : ℝ)|=(5264146217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_1 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336257727/2500000000 : ℝ)*x 0 + (-2275407709/10000000000 : ℝ)*x 1 + (1052829289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336257727/2500000000 : ℝ)^1031 ≤ (10864907780679/25000000000000 : ℝ)^775 := by
    have hnat : (1336257727 : ℕ)^1031*25000000000000^775 ≤ 10864907780679^775*2500000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336257727 2500000000 10864907780679 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275407709/10000000000 : ℝ)^1031 ≤ (2790688513561/20000000000000 : ℝ)^775 := by
    have hnat : (2275407709 : ℕ)^1031*20000000000000^775 ≤ 2790688513561^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275407709 10000000000 2790688513561 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052829289/2000000000 : ℝ)^1031 ≤ (42586926287569/100000000000000 : ℝ)^775 := by
    have hnat : (1052829289 : ℕ)^1031*100000000000000^775 ≤ 42586926287569^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052829289 2000000000 42586926287569 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336257727/2500000000 : ℝ), (-2275407709/10000000000 : ℝ), (1052829289/2000000000 : ℝ)] ![(10864907780679/25000000000000 : ℝ), (2790688513561/20000000000000 : ℝ), (42586926287569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336257727/2500000000 : ℝ)|^1031 ≤ (10864907780679/25000000000000 : ℝ)^775
        have hw : |(1336257727/2500000000 : ℝ)|=(1336257727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2275407709/10000000000 : ℝ)|^1031 ≤ (2790688513561/20000000000000 : ℝ)^775
        have hw : |(-2275407709/10000000000 : ℝ)|=(2275407709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052829289/2000000000 : ℝ)|^1031 ≤ (42586926287569/100000000000000 : ℝ)^775
        have hw : |(1052829289/2000000000 : ℝ)|=(1052829289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_2 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345030999/10000000000 : ℝ)*x 0 + (5264146283/10000000000 : ℝ)*x 1 + (-2275407803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345030999/10000000000 : ℝ)^1031 ≤ (43459632107031/100000000000000 : ℝ)^775 := by
    have hnat : (5345030999 : ℕ)^1031*100000000000000^775 ≤ 43459632107031^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345030999 10000000000 43459632107031 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264146283/10000000000 : ℝ)^1031 ≤ (10646731136019/25000000000000 : ℝ)^775 := by
    have hnat : (5264146283 : ℕ)^1031*25000000000000^775 ≤ 10646731136019^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264146283 10000000000 10646731136019 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275407803/10000000000 : ℝ)^1031 ≤ (13953443334649/100000000000000 : ℝ)^775 := by
    have hnat : (2275407803 : ℕ)^1031*100000000000000^775 ≤ 13953443334649^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275407803 10000000000 13953443334649 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345030999/10000000000 : ℝ), (5264146283/10000000000 : ℝ), (-2275407803/10000000000 : ℝ)] ![(43459632107031/100000000000000 : ℝ), (10646731136019/25000000000000 : ℝ), (13953443334649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345030999/10000000000 : ℝ)|^1031 ≤ (43459632107031/100000000000000 : ℝ)^775
        have hw : |(5345030999/10000000000 : ℝ)|=(5345030999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264146283/10000000000 : ℝ)|^1031 ≤ (10646731136019/25000000000000 : ℝ)^775
        have hw : |(5264146283/10000000000 : ℝ)|=(5264146283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2275407803/10000000000 : ℝ)|^1031 ≤ (13953443334649/100000000000000 : ℝ)^775
        have hw : |(-2275407803/10000000000 : ℝ)|=(2275407803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_3 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4377071209/10000000000 : ℝ)*x 0 + (4251347679/10000000000 : ℝ)*x 1 + (14083043/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377071209/10000000000 : ℝ)^1031 ≤ (33316429855511/100000000000000 : ℝ)^775 := by
    have hnat : (4377071209 : ℕ)^1031*100000000000000^775 ≤ 33316429855511^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377071209 10000000000 33316429855511 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251347679/10000000000 : ℝ)^1031 ≤ (500772653959/1562500000000 : ℝ)^775 := by
    have hnat : (4251347679 : ℕ)^1031*1562500000000^775 ≤ 500772653959^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251347679 10000000000 500772653959 1562500000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14083043/31250000 : ℝ)^1031 ≤ (34634120276701/100000000000000 : ℝ)^775 := by
    have hnat : (14083043 : ℕ)^1031*100000000000000^775 ≤ 34634120276701^775*31250000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14083043 31250000 34634120276701 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377071209/10000000000 : ℝ), (4251347679/10000000000 : ℝ), (14083043/31250000 : ℝ)] ![(33316429855511/100000000000000 : ℝ), (500772653959/1562500000000 : ℝ), (34634120276701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377071209/10000000000 : ℝ)|^1031 ≤ (33316429855511/100000000000000 : ℝ)^775
        have hw : |(4377071209/10000000000 : ℝ)|=(4377071209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251347679/10000000000 : ℝ)|^1031 ≤ (500772653959/1562500000000 : ℝ)^775
        have hw : |(4251347679/10000000000 : ℝ)|=(4251347679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14083043/31250000 : ℝ)|^1031 ≤ (34634120276701/100000000000000 : ℝ)^775
        have hw : |(14083043/31250000 : ℝ)|=(14083043/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_4 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209191041/10000000000 : ℝ)*x 0 + (5264473687/10000000000 : ℝ)*x 1 + (5394329341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209191041/10000000000 : ℝ)^1031 ≤ (13415866126267/100000000000000 : ℝ)^775 := by
    have hnat : (2209191041 : ℕ)^1031*100000000000000^775 ≤ 13415866126267^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209191041 10000000000 13415866126267 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264473687/10000000000 : ℝ)^1031 ≤ (21295224100973/50000000000000 : ℝ)^775 := by
    have hnat : (5264473687 : ℕ)^1031*50000000000000^775 ≤ 21295224100973^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264473687 10000000000 21295224100973 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394329341/10000000000 : ℝ)^1031 ≤ (1759747426147/4000000000000 : ℝ)^775 := by
    have hnat : (5394329341 : ℕ)^1031*4000000000000^775 ≤ 1759747426147^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394329341 10000000000 1759747426147 4000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209191041/10000000000 : ℝ), (5264473687/10000000000 : ℝ), (5394329341/10000000000 : ℝ)] ![(13415866126267/100000000000000 : ℝ), (21295224100973/50000000000000 : ℝ), (1759747426147/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209191041/10000000000 : ℝ)|^1031 ≤ (13415866126267/100000000000000 : ℝ)^775
        have hw : |(-2209191041/10000000000 : ℝ)|=(2209191041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264473687/10000000000 : ℝ)|^1031 ≤ (21295224100973/50000000000000 : ℝ)^775
        have hw : |(5264473687/10000000000 : ℝ)|=(5264473687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394329341/10000000000 : ℝ)|^1031 ≤ (1759747426147/4000000000000 : ℝ)^775
        have hw : |(5394329341/10000000000 : ℝ)|=(5394329341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_5 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312187101/10000000000 : ℝ)*x 0 + (-1072612403/5000000000 : ℝ)*x 1 + (134858219/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312187101/10000000000 : ℝ)^1031 ≤ (43104732196803/100000000000000 : ℝ)^775 := by
    have hnat : (5312187101 : ℕ)^1031*100000000000000^775 ≤ 43104732196803^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312187101 10000000000 43104732196803 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072612403/5000000000 : ℝ)^1031 ≤ (50396829827/390625000000 : ℝ)^775 := by
    have hnat : (1072612403 : ℕ)^1031*390625000000^775 ≤ 50396829827^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072612403 5000000000 50396829827 390625000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134858219/250000000 : ℝ)^1031 ≤ (21996839675057/50000000000000 : ℝ)^775 := by
    have hnat : (134858219 : ℕ)^1031*50000000000000^775 ≤ 21996839675057^775*250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134858219 250000000 21996839675057 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312187101/10000000000 : ℝ), (-1072612403/5000000000 : ℝ), (134858219/250000000 : ℝ)] ![(43104732196803/100000000000000 : ℝ), (50396829827/390625000000 : ℝ), (21996839675057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312187101/10000000000 : ℝ)|^1031 ≤ (43104732196803/100000000000000 : ℝ)^775
        have hw : |(5312187101/10000000000 : ℝ)|=(5312187101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072612403/5000000000 : ℝ)|^1031 ≤ (50396829827/390625000000 : ℝ)^775
        have hw : |(-1072612403/5000000000 : ℝ)|=(1072612403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134858219/250000000 : ℝ)|^1031 ≤ (21996839675057/50000000000000 : ℝ)^775
        have hw : |(134858219/250000000 : ℝ)|=(134858219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_6 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312186827/10000000000 : ℝ)*x 0 + (5394329263/10000000000 : ℝ)*x 1 + (-1072612247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312186827/10000000000 : ℝ)^1031 ≤ (43104729239069/100000000000000 : ℝ)^775 := by
    have hnat : (5312186827 : ℕ)^1031*100000000000000^775 ≤ 43104729239069^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312186827 10000000000 43104729239069 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394329263/10000000000 : ℝ)^1031 ≤ (21996842403707/50000000000000 : ℝ)^775 := by
    have hnat : (5394329263 : ℕ)^1031*50000000000000^775 ≤ 21996842403707^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394329263 10000000000 21996842403707 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072612247/5000000000 : ℝ)^1031 ≤ (6450792969749/50000000000000 : ℝ)^775 := by
    have hnat : (1072612247 : ℕ)^1031*50000000000000^775 ≤ 6450792969749^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072612247 5000000000 6450792969749 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312186827/10000000000 : ℝ), (5394329263/10000000000 : ℝ), (-1072612247/5000000000 : ℝ)] ![(43104729239069/100000000000000 : ℝ), (21996842403707/50000000000000 : ℝ), (6450792969749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312186827/10000000000 : ℝ)|^1031 ≤ (43104729239069/100000000000000 : ℝ)^775
        have hw : |(5312186827/10000000000 : ℝ)|=(5312186827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394329263/10000000000 : ℝ)|^1031 ≤ (21996842403707/50000000000000 : ℝ)^775
        have hw : |(5394329263/10000000000 : ℝ)|=(5394329263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1072612247/5000000000 : ℝ)|^1031 ≤ (6450792969749/50000000000000 : ℝ)^775
        have hw : |(-1072612247/5000000000 : ℝ)|=(1072612247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s7_7 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (273567511/625000000 : ℝ)*x 0 + (4505934761/10000000000 : ℝ)*x 1 + (4251990019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273567511/625000000 : ℝ)^1031 ≤ (6663304130821/20000000000000 : ℝ)^775 := by
    have hnat : (273567511 : ℕ)^1031*20000000000000^775 ≤ 6663304130821^775*625000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273567511 625000000 6663304130821 20000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505934761/10000000000 : ℝ)^1031 ≤ (8656896849301/25000000000000 : ℝ)^775 := by
    have hnat : (4505934761 : ℕ)^1031*25000000000000^775 ≤ 8656896849301^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505934761 10000000000 8656896849301 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251990019/10000000000 : ℝ)^1031 ≤ (32055891942411/100000000000000 : ℝ)^775 := by
    have hnat : (4251990019 : ℕ)^1031*100000000000000^775 ≤ 32055891942411^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251990019 10000000000 32055891942411 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273567511/625000000 : ℝ), (4505934761/10000000000 : ℝ), (4251990019/10000000000 : ℝ)] ![(6663304130821/20000000000000 : ℝ), (8656896849301/25000000000000 : ℝ), (32055891942411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273567511/625000000 : ℝ)|^1031 ≤ (6663304130821/20000000000000 : ℝ)^775
        have hw : |(273567511/625000000 : ℝ)|=(273567511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505934761/10000000000 : ℝ)|^1031 ≤ (8656896849301/25000000000000 : ℝ)^775
        have hw : |(4505934761/10000000000 : ℝ)|=(4505934761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251990019/10000000000 : ℝ)|^1031 ≤ (32055891942411/100000000000000 : ℝ)^775
        have hw : |(4251990019/10000000000 : ℝ)|=(4251990019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1055_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6999/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1403/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1403/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1403/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1403/12500 : ℝ) ^ (8247/2048 : ℝ) ≤ (2993035705908269/20000000000000000000 : ℝ) := by
    have hpowers : (1403/12500 : ℝ)^8247 ≤ (2993035705908269/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1403 : ℕ)^8247*20000000000000000000^2048 ≤ 2993035705908269^2048*12500^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 12500 2993035705908269 20000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/12500 : ℝ)) (X := (2993035705908269/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14009/100000 : ℝ) ^ (8247/2048 : ℝ) ≤ (36534646084990491/100000000000000000000 : ℝ) := by
    have hpowers : (14009/100000 : ℝ)^8247 ≤ (36534646084990491/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14009 : ℕ)^8247*100000000000000000000^2048 ≤ 36534646084990491^2048*100000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14009 100000 36534646084990491 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14009/100000 : ℝ)) (X := (36534646084990491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002993035705908269/10000000000000000000 : ℝ) ≤ (10000743185124551/10000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (10002993035705908269/10000000000000000000 : ℝ)^2048 ≤ (10000743185124551/10000000000000000 : ℝ)^8247 := by
      have hnat : (10002993035705908269 : ℕ)^2048*10000000000000000^8247 ≤ 10000743185124551^8247*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002993035705908269 10000000000000000000 10000743185124551 10000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000743185124551/10000000000000000 : ℝ)) (X := (10002993035705908269/10000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012874956153632959/25000000000000000000 : ℝ) ≤ (5000639330862887/5000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (25012874956153632959/25000000000000000000 : ℝ)^2048 ≤ (5000639330862887/5000000000000000 : ℝ)^8247 := by
      have hnat : (25012874956153632959 : ℕ)^2048*5000000000000000^8247 ≤ 5000639330862887^8247*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012874956153632959 25000000000000000000 5000639330862887 5000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000639330862887/5000000000000000 : ℝ)) (X := (25012874956153632959/25000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036534646084990491/50000000000000000000 : ℝ) ≤ (10001814138326997/10000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50036534646084990491/50000000000000000000 : ℝ)^2048 ≤ (10001814138326997/10000000000000000 : ℝ)^8247 := by
      have hnat : (50036534646084990491 : ℕ)^2048*10000000000000000^8247 ≤ 10001814138326997^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036534646084990491 50000000000000000000 10001814138326997 10000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001814138326997/10000000000000000 : ℝ)) (X := (50036534646084990491/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2993035705908269/20000000000000000000 : ℝ) ≤ ((27840049391827620631/27850000000000000000 : ℝ)+2*(535476601223/278500000000000 : ℝ)*(1403/12500 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (27840049391827620631/27850000000000000000 : ℝ)+2*(535476601223/278500000000000 : ℝ)*(1403/12500 : ℝ)=(10000743185124551/10000000000000000 : ℝ) by norm_num, show 1+2*(2993035705908269/20000000000000000000 : ℝ)=(10002993035705908269/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36534646084990491/100000000000000000000 : ℝ)+(2993035705908269/20000000000000000000 : ℝ) ≤ ((27840049391827620631/27850000000000000000 : ℝ)+(535476601223/278500000000000 : ℝ)*((14009/100000 : ℝ)+(1403/12500 : ℝ)))^(8247/2048 : ℝ) := by
    rw [show (27840049391827620631/27850000000000000000 : ℝ)+(535476601223/278500000000000 : ℝ)*((14009/100000 : ℝ)+(1403/12500 : ℝ))=(5000639330862887/5000000000000000 : ℝ) by norm_num, show 1+(36534646084990491/100000000000000000000 : ℝ)+(2993035705908269/20000000000000000000 : ℝ)=(25012874956153632959/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36534646084990491/100000000000000000000 : ℝ) ≤ ((27840049391827620631/27850000000000000000 : ℝ)+2*(535476601223/278500000000000 : ℝ)*(14009/100000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (27840049391827620631/27850000000000000000 : ℝ)+2*(535476601223/278500000000000 : ℝ)*(14009/100000 : ℝ)=(10001814138326997/10000000000000000 : ℝ) by norm_num, show 1+2*(36534646084990491/100000000000000000000 : ℝ)=(50036534646084990491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27840049391827620631/27850000000000000000 : ℝ)*(X 1 0+X 2 0)+(535476601223/278500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (27840049391827620631/27850000000000000000 : ℝ)) (alpha := (535476601223/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27840049391827620631/27850000000000000000 : ℝ)*(X 0 1+X 2 1)+(535476601223/278500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (27840049391827620631/27850000000000000000 : ℝ)) (alpha := (535476601223/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27840049391827620631/27850000000000000000 : ℝ)*(X 0 2+X 1 2)+(535476601223/278500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (1403/12500 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (27840049391827620631/27850000000000000000 : ℝ)) (alpha := (535476601223/278500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-44183717/200000000 : ℝ)*X 0 0+(1078931609/2000000000 : ℝ)*X 0 1+(5264146217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336257727/2500000000 : ℝ)*X 1 0+(-2275407709/10000000000 : ℝ)*X 1 1+(1052829289/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345030999/10000000000 : ℝ)*X 2 0+(5264146283/10000000000 : ℝ)*X 2 1+(-2275407803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377071209/10000000000 : ℝ)*X 0 0+(4251347679/10000000000 : ℝ)*X 0 1+(14083043/31250000 : ℝ)*X 0 2+(4377071209/10000000000 : ℝ)*X 1 0+(4251347679/10000000000 : ℝ)*X 1 1+(14083043/31250000 : ℝ)*X 1 2+(4377071209/10000000000 : ℝ)*X 2 0+(4251347679/10000000000 : ℝ)*X 2 1+(14083043/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2209191041/10000000000 : ℝ)*X 0 0+(5264473687/10000000000 : ℝ)*X 0 1+(5394329341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312187101/10000000000 : ℝ)*X 1 0+(-1072612403/5000000000 : ℝ)*X 1 1+(134858219/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312186827/10000000000 : ℝ)*X 2 0+(5394329263/10000000000 : ℝ)*X 2 1+(-1072612247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273567511/625000000 : ℝ)*X 0 0+(4505934761/10000000000 : ℝ)*X 0 1+(4251990019/10000000000 : ℝ)*X 0 2+(273567511/625000000 : ℝ)*X 1 0+(4505934761/10000000000 : ℝ)*X 1 1+(4251990019/10000000000 : ℝ)*X 1 2+(273567511/625000000 : ℝ)*X 2 0+(4505934761/10000000000 : ℝ)*X 2 1+(4251990019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (437479208953088823511563213/87031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66047973/5000000000000 : ℝ)*(base19) + (1367501181/100000000000000 : ℝ)*(base23) + (250508337/100000000000000 : ℝ)*(upper3) + (28031/62500000000 : ℝ)*(upper4) + (8456719/12500000000000 : ℝ)*(upper5) + (5790182515632143/100000000000000 : ℝ)*(major0) + (5790182515632143/100000000000000 : ℝ)*(major1) + (361886407227009/6250000000000 : ℝ)*(major2) + (7662188990456073/100000000000000 : ℝ)*(sp0) + (766222990059191/10000000000000 : ℝ)*(sp1) + (7662229854050189/100000000000000 : ℝ)*(sp2) + (979527956318761/25000000000000 : ℝ)*(sp3) + (42231095297/100000000000000 : ℝ)*(sp4) + (21816881493/100000000000000 : ℝ)*(sp7) + (1959066821078269/50000000000000 : ℝ)*(f.failure) + (766223122155137/10000000000000 : ℝ)*(f.sum) + (3647133752449/27850000000000000000000000000 : ℝ)*base66 + (24456658413040257767/2785000000000000000000000000000000 : ℝ)*base68 + (205227414459066429/174062500000000000000000000000000 : ℝ)*base69 + (24599910098775257767/2785000000000000000000000000000000 : ℝ)*base72 + (90684238399851/27850000000000000000000000000 : ℝ)*base73 + (2387897217139066429/174062500000000000000000000000000 : ℝ)*base75 + (32544720372267442233/2785000000000000000000000000000000 : ℝ)*base77 + (36076660822882442233/2785000000000000000000000000000000 : ℝ)*base79 + (62960038278889/13925000000000000000000000000 : ℝ)*base81 + (9143093/5000000000000000000000 : ℝ)*base89 + (9143093/5000000000000000000000 : ℝ)*base91 + (40856907/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4482069396804160767169353/21757812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (242862889/25000000000000 : ℝ)*(base19) + (1436031243/100000000000000 : ℝ)*(base23) + (216912981/50000000000000 : ℝ)*(upper2) + (28337417/25000000000000 : ℝ)*(upper4) + (216527499/100000000000000 : ℝ)*(lower5) + (363709760952567/6250000000000 : ℝ)*(major0) + (363709760952567/6250000000000 : ℝ)*(major1) + (363709760952567/6250000000000 : ℝ)*(major2) + (41809558897/100000000000000 : ℝ)*(sp2) + (498737983/10000000000000 : ℝ)*(sp3) + (962604662940041/12500000000000 : ℝ)*(sp4) + (1925209083017193/25000000000000 : ℝ)*(sp5) + (7700794057930187/100000000000000 : ℝ)*(sp6) + (492233756589421/12500000000000 : ℝ)*(sp7) + (1968937520047599/50000000000000 : ℝ)*(f.failure) + (962604662940041/12500000000000 : ℝ)*(f.sum) + (22579798402653/6962500000000000000000000000 : ℝ)*base65 + (1097804486824915223/174062500000000000000000000000000 : ℝ)*base68 + (1407650651544290223/174062500000000000000000000000000 : ℝ)*base70 + (3251123010490084777/174062500000000000000000000000000 : ℝ)*base71 + (4651461190503/6962500000000000000000000000 : ℝ)*base73 + (4745671386451790223/174062500000000000000000000000000 : ℝ)*base76 + (1968138402778665223/174062500000000000000000000000000 : ℝ)*base78 + (2356569256097415223/174062500000000000000000000000000 : ℝ)*base80 + (55019935256719/13925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (22761897/5000000000000000000000 : ℝ)*base90 + (22761897/5000000000000000000000 : ℝ)*base92 + (22761897/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1055_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1403/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1055_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1055_s8_0 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209197433/10000000000 : ℝ)*x 0 + (5394543799/10000000000 : ℝ)*x 1 + (1052850539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209197433/10000000000 : ℝ)^1031 ≤ (3353979441363/25000000000000 : ℝ)^775 := by
    have hnat : (2209197433 : ℕ)^1031*25000000000000^775 ≤ 3353979441363^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209197433 10000000000 3353979441363 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394543799/10000000000 : ℝ)^1031 ≤ (4399601243171/10000000000000 : ℝ)^775 := by
    have hnat : (5394543799 : ℕ)^1031*10000000000000^775 ≤ 4399601243171^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394543799 10000000000 4399601243171 10000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052850539/2000000000 : ℝ)^1031 ≤ (42588069786289/100000000000000 : ℝ)^775 := by
    have hnat : (1052850539 : ℕ)^1031*100000000000000^775 ≤ 42588069786289^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052850539 2000000000 42588069786289 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209197433/10000000000 : ℝ), (5394543799/10000000000 : ℝ), (1052850539/2000000000 : ℝ)] ![(3353979441363/25000000000000 : ℝ), (4399601243171/10000000000000 : ℝ), (42588069786289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209197433/10000000000 : ℝ)|^1031 ≤ (3353979441363/25000000000000 : ℝ)^775
        have hw : |(-2209197433/10000000000 : ℝ)|=(2209197433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394543799/10000000000 : ℝ)|^1031 ≤ (4399601243171/10000000000000 : ℝ)^775
        have hw : |(5394543799/10000000000 : ℝ)|=(5394543799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052850539/2000000000 : ℝ)|^1031 ≤ (42588069786289/100000000000000 : ℝ)^775
        have hw : |(1052850539/2000000000 : ℝ)|=(1052850539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_1 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345001843/10000000000 : ℝ)*x 0 + (-284413251/1250000000 : ℝ)*x 1 + (2632126373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345001843/10000000000 : ℝ)^1031 ≤ (21729658368533/50000000000000 : ℝ)^775 := by
    have hnat : (5345001843 : ℕ)^1031*50000000000000^775 ≤ 21729658368533^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345001843 10000000000 21729658368533 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284413251/1250000000 : ℝ)^1031 ≤ (3488153226487/25000000000000 : ℝ)^775 := by
    have hnat : (284413251 : ℕ)^1031*25000000000000^775 ≤ 3488153226487^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284413251 1250000000 3488153226487 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632126373/5000000000 : ℝ)^1031 ≤ (4258807033517/10000000000000 : ℝ)^775 := by
    have hnat : (2632126373 : ℕ)^1031*10000000000000^775 ≤ 4258807033517^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632126373 5000000000 4258807033517 10000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345001843/10000000000 : ℝ), (-284413251/1250000000 : ℝ), (2632126373/5000000000 : ℝ)] ![(21729658368533/50000000000000 : ℝ), (3488153226487/25000000000000 : ℝ), (4258807033517/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345001843/10000000000 : ℝ)|^1031 ≤ (21729658368533/50000000000000 : ℝ)^775
        have hw : |(5345001843/10000000000 : ℝ)|=(5345001843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284413251/1250000000 : ℝ)|^1031 ≤ (3488153226487/25000000000000 : ℝ)^775
        have hw : |(-284413251/1250000000 : ℝ)|=(284413251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632126373/5000000000 : ℝ)|^1031 ≤ (4258807033517/10000000000000 : ℝ)^775
        have hw : |(2632126373/5000000000 : ℝ)|=(2632126373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_2 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345001987/10000000000 : ℝ)*x 0 + (2632126331/5000000000 : ℝ)*x 1 + (-2275305929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345001987/10000000000 : ℝ)^1031 ≤ (43459318294661/100000000000000 : ℝ)^775 := by
    have hnat : (5345001987 : ℕ)^1031*100000000000000^775 ≤ 43459318294661^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345001987 10000000000 43459318294661 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632126331/5000000000 : ℝ)^1031 ≤ (4258806943113/10000000000000 : ℝ)^775 := by
    have hnat : (2632126331 : ℕ)^1031*10000000000000^775 ≤ 4258806943113^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632126331 5000000000 4258806943113 10000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275305929/10000000000 : ℝ)^1031 ≤ (6976306130741/50000000000000 : ℝ)^775 := by
    have hnat : (2275305929 : ℕ)^1031*50000000000000^775 ≤ 6976306130741^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275305929 10000000000 6976306130741 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345001987/10000000000 : ℝ), (2632126331/5000000000 : ℝ), (-2275305929/10000000000 : ℝ)] ![(43459318294661/100000000000000 : ℝ), (4258806943113/10000000000000 : ℝ), (6976306130741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345001987/10000000000 : ℝ)|^1031 ≤ (43459318294661/100000000000000 : ℝ)^775
        have hw : |(5345001987/10000000000 : ℝ)|=(5345001987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632126331/5000000000 : ℝ)|^1031 ≤ (4258806943113/10000000000000 : ℝ)^775
        have hw : |(2632126331/5000000000 : ℝ)|=(2632126331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2275305929/10000000000 : ℝ)|^1031 ≤ (6976306130741/50000000000000 : ℝ)^775
        have hw : |(-2275305929/10000000000 : ℝ)|=(2275305929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_3 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4377076861/10000000000 : ℝ)*x 0 + (2125781247/5000000000 : ℝ)*x 1 + (4506357441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377076861/10000000000 : ℝ)^1031 ≤ (33316487086869/100000000000000 : ℝ)^775 := by
    have hnat : (4377076861 : ℕ)^1031*100000000000000^775 ≤ 33316487086869^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377076861 10000000000 33316487086869 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125781247/5000000000 : ℝ)^1031 ≤ (32051604217689/100000000000000 : ℝ)^775 := by
    have hnat : (2125781247 : ℕ)^1031*100000000000000^775 ≤ 32051604217689^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125781247 5000000000 32051604217689 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506357441/10000000000 : ℝ)^1031 ≤ (8657977170089/25000000000000 : ℝ)^775 := by
    have hnat : (4506357441 : ℕ)^1031*25000000000000^775 ≤ 8657977170089^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506357441 10000000000 8657977170089 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377076861/10000000000 : ℝ), (2125781247/5000000000 : ℝ), (4506357441/10000000000 : ℝ)] ![(33316487086869/100000000000000 : ℝ), (32051604217689/100000000000000 : ℝ), (8657977170089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377076861/10000000000 : ℝ)|^1031 ≤ (33316487086869/100000000000000 : ℝ)^775
        have hw : |(4377076861/10000000000 : ℝ)|=(4377076861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125781247/5000000000 : ℝ)|^1031 ≤ (32051604217689/100000000000000 : ℝ)^775
        have hw : |(2125781247/5000000000 : ℝ)|=(2125781247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506357441/10000000000 : ℝ)|^1031 ≤ (8657977170089/25000000000000 : ℝ)^775
        have hw : |(4506357441/10000000000 : ℝ)|=(4506357441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_4 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104601213/5000000000 : ℝ)*x 0 + (1052915737/2000000000 : ℝ)*x 1 + (5394216707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104601213/5000000000 : ℝ)^1031 ≤ (13415958102541/100000000000000 : ℝ)^775 := by
    have hnat : (1104601213 : ℕ)^1031*100000000000000^775 ≤ 13415958102541^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104601213 5000000000 13415958102541 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052915737/2000000000 : ℝ)^1031 ≤ (21295789124687/50000000000000 : ℝ)^775 := by
    have hnat : (1052915737 : ℕ)^1031*50000000000000^775 ≤ 21295789124687^775*2000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052915737 2000000000 21295789124687 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394216707/10000000000 : ℝ)^1031 ≤ (43992463634947/100000000000000 : ℝ)^775 := by
    have hnat : (5394216707 : ℕ)^1031*100000000000000^775 ≤ 43992463634947^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394216707 10000000000 43992463634947 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104601213/5000000000 : ℝ), (1052915737/2000000000 : ℝ), (5394216707/10000000000 : ℝ)] ![(13415958102541/100000000000000 : ℝ), (21295789124687/50000000000000 : ℝ), (43992463634947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104601213/5000000000 : ℝ)|^1031 ≤ (13415958102541/100000000000000 : ℝ)^775
        have hw : |(-1104601213/5000000000 : ℝ)|=(1104601213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052915737/2000000000 : ℝ)|^1031 ≤ (21295789124687/50000000000000 : ℝ)^775
        have hw : |(1052915737/2000000000 : ℝ)|=(1052915737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394216707/10000000000 : ℝ)|^1031 ≤ (43992463634947/100000000000000 : ℝ)^775
        have hw : |(5394216707/10000000000 : ℝ)|=(5394216707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_5 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312213371/10000000000 : ℝ)*x 0 + (-1072670639/5000000000 : ℝ)*x 1 + (5394216733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312213371/10000000000 : ℝ)^1031 ≤ (43105015772481/100000000000000 : ℝ)^775 := by
    have hnat : (5312213371 : ℕ)^1031*100000000000000^775 ≤ 43105015772481^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312213371 10000000000 43105015772481 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072670639/5000000000 : ℝ)^1031 ≤ (3225630075051/25000000000000 : ℝ)^775 := by
    have hnat : (1072670639 : ℕ)^1031*25000000000000^775 ≤ 3225630075051^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072670639 5000000000 3225630075051 25000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394216733/10000000000 : ℝ)^1031 ≤ (5499057989629/12500000000000 : ℝ)^775 := by
    have hnat : (5394216733 : ℕ)^1031*12500000000000^775 ≤ 5499057989629^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394216733 10000000000 5499057989629 12500000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312213371/10000000000 : ℝ), (-1072670639/5000000000 : ℝ), (5394216733/10000000000 : ℝ)] ![(43105015772481/100000000000000 : ℝ), (3225630075051/25000000000000 : ℝ), (5499057989629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312213371/10000000000 : ℝ)|^1031 ≤ (43105015772481/100000000000000 : ℝ)^775
        have hw : |(5312213371/10000000000 : ℝ)|=(5312213371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072670639/5000000000 : ℝ)|^1031 ≤ (3225630075051/25000000000000 : ℝ)^775
        have hw : |(-1072670639/5000000000 : ℝ)|=(1072670639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394216733/10000000000 : ℝ)|^1031 ≤ (5499057989629/12500000000000 : ℝ)^775
        have hw : |(5394216733/10000000000 : ℝ)|=(5394216733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_6 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (53122121/100000000 : ℝ)*x 0 + (5394216521/10000000000 : ℝ)*x 1 + (-26816791/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53122121/100000000 : ℝ)^1031 ≤ (43105002052459/100000000000000 : ℝ)^775 := by
    have hnat : (53122121 : ℕ)^1031*100000000000000^775 ≤ 43105002052459^775*100000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53122121 100000000 43105002052459 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394216521/10000000000 : ℝ)^1031 ≤ (43992461616953/100000000000000 : ℝ)^775 := by
    have hnat : (5394216521 : ℕ)^1031*100000000000000^775 ≤ 43992461616953^775*10000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394216521 10000000000 43992461616953 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26816791/125000000 : ℝ)^1031 ≤ (12902536317871/100000000000000 : ℝ)^775 := by
    have hnat : (26816791 : ℕ)^1031*100000000000000^775 ≤ 12902536317871^775*125000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26816791 125000000 12902536317871 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53122121/100000000 : ℝ), (5394216521/10000000000 : ℝ), (-26816791/125000000 : ℝ)] ![(43105002052459/100000000000000 : ℝ), (43992461616953/100000000000000 : ℝ), (12902536317871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53122121/100000000 : ℝ)|^1031 ≤ (43105002052459/100000000000000 : ℝ)^775
        have hw : |(53122121/100000000 : ℝ)|=(53122121/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394216521/10000000000 : ℝ)|^1031 ≤ (43992461616953/100000000000000 : ℝ)^775
        have hw : |(5394216521/10000000000 : ℝ)|=(5394216521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26816791/125000000 : ℝ)|^1031 ≤ (12902536317871/100000000000000 : ℝ)^775
        have hw : |(-26816791/125000000 : ℝ)|=(26816791/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1055_s8_7 (p : ℝ) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ)) (x : Fin 3 → ℝ) :
    (175083417/400000000 : ℝ)*x 0 + (2252859901/5000000000 : ℝ)*x 1 + (531525479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175083417/400000000 : ℝ)^1031 ≤ (33316573804777/100000000000000 : ℝ)^775 := by
    have hnat : (175083417 : ℕ)^1031*100000000000000^775 ≤ 33316573804777^775*400000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175083417 400000000 33316573804777 100000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252859901/5000000000 : ℝ)^1031 ≤ (17312694904011/50000000000000 : ℝ)^775 := by
    have hnat : (2252859901 : ℕ)^1031*50000000000000^775 ≤ 17312694904011^775*5000000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252859901 5000000000 17312694904011 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531525479/1250000000 : ℝ)^1031 ≤ (16029018182333/50000000000000 : ℝ)^775 := by
    have hnat : (531525479 : ℕ)^1031*50000000000000^775 ≤ 16029018182333^775*1250000000^1031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531525479 1250000000 16029018182333 50000000000000 1031 775 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1031/256 : ℝ)) 1031 775 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175083417/400000000 : ℝ), (2252859901/5000000000 : ℝ), (531525479/1250000000 : ℝ)] ![(33316573804777/100000000000000 : ℝ), (17312694904011/50000000000000 : ℝ), (16029018182333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175083417/400000000 : ℝ)|^1031 ≤ (33316573804777/100000000000000 : ℝ)^775
        have hw : |(175083417/400000000 : ℝ)|=(175083417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252859901/5000000000 : ℝ)|^1031 ≤ (17312694904011/50000000000000 : ℝ)^775
        have hw : |(2252859901/5000000000 : ℝ)|=(2252859901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531525479/1250000000 : ℝ)|^1031 ≤ (16029018182333/50000000000000 : ℝ)^775
        have hw : |(531525479/1250000000 : ℝ)|=(531525479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1055_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2809/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3499/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5617/50000 : ℝ) ^ (8247/2048 : ℝ) ≤ (7509470909972253/50000000000000000000 : ℝ) := by
    have hpowers : (5617/50000 : ℝ)^8247 ≤ (7509470909972253/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5617 : ℕ)^8247*50000000000000000000^2048 ≤ 7509470909972253^2048*50000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5617 50000 7509470909972253 50000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5617/50000 : ℝ)) (X := (7509470909972253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/50000 : ℝ) ^ (8247/2048 : ℝ) ≤ (36419263472854869/100000000000000000000 : ℝ) := by
    have hpowers : (6999/50000 : ℝ)^8247 ≤ (36419263472854869/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6999 : ℕ)^8247*100000000000000000000^2048 ≤ 36419263472854869^2048*50000^8247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 50000 36419263472854869 100000000000000000000 8247 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/50000 : ℝ)) (X := (36419263472854869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007509470909972253/25000000000000000000 : ℝ) ≤ (10000745854759793/10000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (25007509470909972253/25000000000000000000 : ℝ)^2048 ≤ (10000745854759793/10000000000000000 : ℝ)^8247 := by
      have hnat : (25007509470909972253 : ℕ)^2048*10000000000000000^8247 ≤ 10000745854759793^8247*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007509470909972253 25000000000000000000 10000745854759793 10000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000745854759793/10000000000000000 : ℝ)) (X := (25007509470909972253/25000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (160082301128468479/160000000000000000 : ℝ) ≤ (1250159641513511/1250000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (160082301128468479/160000000000000000 : ℝ)^2048 ≤ (1250159641513511/1250000000000000 : ℝ)^8247 := by
      have hnat : (160082301128468479 : ℕ)^2048*1250000000000000^8247 ≤ 1250159641513511^8247*160000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160082301128468479 160000000000000000 1250159641513511 1250000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250159641513511/1250000000000000 : ℝ)) (X := (160082301128468479/160000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036419263472854869/50000000000000000000 : ℝ) ≤ (10001808409456383/10000000000000000 : ℝ) ^ (8247/2048 : ℝ) := by
    have hpowers : (50036419263472854869/50000000000000000000 : ℝ)^2048 ≤ (10001808409456383/10000000000000000 : ℝ)^8247 := by
      have hnat : (50036419263472854869 : ℕ)^2048*10000000000000000^8247 ≤ 10001808409456383^8247*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036419263472854869 50000000000000000000 10001808409456383 10000000000000000 2048 8247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001808409456383/10000000000000000 : ℝ)) (X := (50036419263472854869/50000000000000000000 : ℝ)) (by norm_num) 8247 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7509470909972253/50000000000000000000 : ℝ) ≤ ((1726882800193410987/1727500000000000000 : ℝ)+2*(106255469659/55280000000000 : ℝ)*(5617/50000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (1726882800193410987/1727500000000000000 : ℝ)+2*(106255469659/55280000000000 : ℝ)*(5617/50000 : ℝ)=(10000745854759793/10000000000000000 : ℝ) by norm_num, show 1+2*(7509470909972253/50000000000000000000 : ℝ)=(25007509470909972253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36419263472854869/100000000000000000000 : ℝ)+(7509470909972253/50000000000000000000 : ℝ) ≤ ((1726882800193410987/1727500000000000000 : ℝ)+(106255469659/55280000000000 : ℝ)*((6999/50000 : ℝ)+(5617/50000 : ℝ)))^(8247/2048 : ℝ) := by
    rw [show (1726882800193410987/1727500000000000000 : ℝ)+(106255469659/55280000000000 : ℝ)*((6999/50000 : ℝ)+(5617/50000 : ℝ))=(1250159641513511/1250000000000000 : ℝ) by norm_num, show 1+(36419263472854869/100000000000000000000 : ℝ)+(7509470909972253/50000000000000000000 : ℝ)=(160082301128468479/160000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36419263472854869/100000000000000000000 : ℝ) ≤ ((1726882800193410987/1727500000000000000 : ℝ)+2*(106255469659/55280000000000 : ℝ)*(6999/50000 : ℝ))^(8247/2048 : ℝ) := by
    rw [show (1726882800193410987/1727500000000000000 : ℝ)+2*(106255469659/55280000000000 : ℝ)*(6999/50000 : ℝ)=(10001808409456383/10000000000000000 : ℝ) by norm_num, show 1+2*(36419263472854869/100000000000000000000 : ℝ)=(50036419263472854869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1726882800193410987/1727500000000000000 : ℝ)*(X 1 0+X 2 0)+(106255469659/55280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (1726882800193410987/1727500000000000000 : ℝ)) (alpha := (106255469659/55280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1726882800193410987/1727500000000000000 : ℝ)*(X 0 1+X 2 1)+(106255469659/55280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (1726882800193410987/1727500000000000000 : ℝ)) (alpha := (106255469659/55280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1726882800193410987/1727500000000000000 : ℝ)*(X 0 2+X 1 2)+(106255469659/55280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8247/2048 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (1726882800193410987/1727500000000000000 : ℝ)) (alpha := (106255469659/55280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209197433/10000000000 : ℝ)*X 0 0+(5394543799/10000000000 : ℝ)*X 0 1+(1052850539/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345001843/10000000000 : ℝ)*X 1 0+(-284413251/1250000000 : ℝ)*X 1 1+(2632126373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345001987/10000000000 : ℝ)*X 2 0+(2632126331/5000000000 : ℝ)*X 2 1+(-2275305929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377076861/10000000000 : ℝ)*X 0 0+(2125781247/5000000000 : ℝ)*X 0 1+(4506357441/10000000000 : ℝ)*X 0 2+(4377076861/10000000000 : ℝ)*X 1 0+(2125781247/5000000000 : ℝ)*X 1 1+(4506357441/10000000000 : ℝ)*X 1 2+(4377076861/10000000000 : ℝ)*X 2 0+(2125781247/5000000000 : ℝ)*X 2 1+(4506357441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104601213/5000000000 : ℝ)*X 0 0+(1052915737/2000000000 : ℝ)*X 0 1+(5394216707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312213371/10000000000 : ℝ)*X 1 0+(-1072670639/5000000000 : ℝ)*X 1 1+(5394216733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53122121/100000000 : ℝ)*X 2 0+(5394216521/10000000000 : ℝ)*X 2 1+(-26816791/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((175083417/400000000 : ℝ)*X 0 0+(2252859901/5000000000 : ℝ)*X 0 1+(531525479/1250000000 : ℝ)*X 0 2+(175083417/400000000 : ℝ)*X 1 0+(2252859901/5000000000 : ℝ)*X 1 1+(531525479/1250000000 : ℝ)*X 1 2+(175083417/400000000 : ℝ)*X 2 0+(2252859901/5000000000 : ℝ)*X 2 1+(531525479/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1055_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (715113072672623805278435211/86375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (803541147/50000000000000 : ℝ)*(base19) + (1651276537/100000000000000 : ℝ)*(base23) + (43450609/50000000000000 : ℝ)*(lower2) + (155955853/100000000000000 : ℝ)*(upper3) + (198873107/100000000000000 : ℝ)*(upper5) + (5799992910486001/100000000000000 : ℝ)*(major0) + (5799992910486001/100000000000000 : ℝ)*(major1) + (2899996455243001/50000000000000 : ℝ)*(major2) + (7675163776763149/100000000000000 : ℝ)*(sp0) + (119925183468199/1562500000000 : ℝ)*(sp1) + (7675211697770493/100000000000000 : ℝ)*(sp2) + (981186949680137/25000000000000 : ℝ)*(sp3) + (49572283881/100000000000000 : ℝ)*(sp4) + (6099308043/25000000000000 : ℝ)*(sp7) + (49059652449409/1250000000000 : ℝ)*(f.failure) + (767521334904703/10000000000000 : ℝ)*(f.sum) + (15749305071463/5528000000000000000000000000 : ℝ)*base66 + (1104689101648719513/172750000000000000000000000000000 : ℝ)*base68 + (285538380505586931/43187500000000000000000000000000 : ℝ)*base69 + (880184097184719513/172750000000000000000000000000000 : ℝ)*base72 + (14553965575473/5528000000000000000000000000 : ℝ)*base73 + (335766868625288069/43187500000000000000000000000000 : ℝ)*base76 + (119488631935186737/172750000000000000000000000000000 : ℝ)*base77 + (1942212913958063263/172750000000000000000000000000000 : ℝ)*base80 + (7123065773559/2764000000000000000000000000 : ℝ)*base81 + (1046327/125000000000000000000 : ℝ)*base90 + (1046327/125000000000000000000 : ℝ)*base92 + (2296327/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (914992304632097930191466673/86375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30648557/20000000000000 : ℝ)*(base19) + (292866263/100000000000000 : ℝ)*(upper1) + (149655013/20000000000000 : ℝ)*(upper2) + (189471371/50000000000000 : ℝ)*(lower4) + (84264219/50000000000000 : ℝ)*(lower5) + (5829170634661131/100000000000000 : ℝ)*(major0) + (5829170634661131/100000000000000 : ℝ)*(major1) + (5829170634661131/100000000000000 : ℝ)*(major2) + (40088201281/100000000000000 : ℝ)*(sp0) + (2174893023/3125000000000 : ℝ)*(sp1) + (1928446120921837/25000000000000 : ℝ)*(sp4) + (7713754822069109/100000000000000 : ℝ)*(sp5) + (771382457188863/10000000000000 : ℝ)*(sp6) + (98612908608129/2500000000000 : ℝ)*(sp7) + (98612908608129/2500000000000 : ℝ)*(f.failure) + (771382457188863/10000000000000 : ℝ)*(f.sum) + (7765874794027/2764000000000000000000000000 : ℝ)*base66 + (414869247439722453/172750000000000000000000000000000 : ℝ)*base68 + (2047639406517722453/172750000000000000000000000000000 : ℝ)*base70 + (1754886103086722453/172750000000000000000000000000000 : ℝ)*base72 + (3065047017009/2764000000000000000000000000 : ℝ)*base73 + (3323414156968222453/172750000000000000000000000000000 : ℝ)*base76 + (2275147278107472453/172750000000000000000000000000000 : ℝ)*base78 + (1131897892619972453/172750000000000000000000000000000 : ℝ)*base80 + (3426205849751/2764000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2979513/250000000000000000000 : ℝ)*base89 + (2979513/250000000000000000000 : ℝ)*base91 + (2979513/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1055_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1055_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1055_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1055_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1055_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1055_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8247/2048 : ℝ) ≤ p) (hpb : p ≤ (1031/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147779097/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1055_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
