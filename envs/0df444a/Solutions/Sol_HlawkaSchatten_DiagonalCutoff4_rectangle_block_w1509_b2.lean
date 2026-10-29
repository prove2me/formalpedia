-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1509_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:57.549238+00:00
-- url     : https://prove2.me/submissions/98c0674e-56e3-4780-8f99-3d4c54f50f81

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
theorem support_rectangle_w1509_s6_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872460131/10000000000 : ℝ)*x 0 + (5433622651/10000000000 : ℝ)*x 1 + (2608741771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872460131/10000000000 : ℝ)^4515 ≤ (357966607139/3125000000000 : ℝ)^3491 := by
    have hnat : (1872460131 : ℕ)^4515*3125000000000^3491 ≤ 357966607139^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872460131 10000000000 357966607139 3125000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433622651/10000000000 : ℝ)^4515 ≤ (908687191531/2000000000000 : ℝ)^3491 := by
    have hnat : (5433622651 : ℕ)^4515*2000000000000^3491 ≤ 908687191531^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433622651 10000000000 908687191531 2000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608741771/5000000000 : ℝ)^4515 ≤ (43110708978887/100000000000000 : ℝ)^3491 := by
    have hnat : (2608741771 : ℕ)^4515*100000000000000^3491 ≤ 43110708978887^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608741771 5000000000 43110708978887 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872460131/10000000000 : ℝ), (5433622651/10000000000 : ℝ), (2608741771/5000000000 : ℝ)] ![(357966607139/3125000000000 : ℝ), (908687191531/2000000000000 : ℝ), (43110708978887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872460131/10000000000 : ℝ)|^4515 ≤ (357966607139/3125000000000 : ℝ)^3491
        have hw : |(-1872460131/10000000000 : ℝ)|=(1872460131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433622651/10000000000 : ℝ)|^4515 ≤ (908687191531/2000000000000 : ℝ)^3491
        have hw : |(5433622651/10000000000 : ℝ)|=(5433622651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608741771/5000000000 : ℝ)|^4515 ≤ (43110708978887/100000000000000 : ℝ)^3491
        have hw : |(2608741771/5000000000 : ℝ)|=(2608741771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675878087/5000000000 : ℝ)*x 0 + (-991581399/5000000000 : ℝ)*x 1 + (130437089/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675878087/5000000000 : ℝ)^4515 ≤ (44550985240297/100000000000000 : ℝ)^3491 := by
    have hnat : (2675878087 : ℕ)^4515*100000000000000^3491 ≤ 44550985240297^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675878087 5000000000 44550985240297 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991581399/5000000000 : ℝ)^4515 ≤ (6169152786059/50000000000000 : ℝ)^3491 := by
    have hnat : (991581399 : ℕ)^4515*50000000000000^3491 ≤ 6169152786059^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991581399 5000000000 6169152786059 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130437089/250000000 : ℝ)^4515 ≤ (21555354585621/50000000000000 : ℝ)^3491 := by
    have hnat : (130437089 : ℕ)^4515*50000000000000^3491 ≤ 21555354585621^3491*250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130437089 250000000 21555354585621 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675878087/5000000000 : ℝ), (-991581399/5000000000 : ℝ), (130437089/250000000 : ℝ)] ![(44550985240297/100000000000000 : ℝ), (6169152786059/50000000000000 : ℝ), (21555354585621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675878087/5000000000 : ℝ)|^4515 ≤ (44550985240297/100000000000000 : ℝ)^3491
        have hw : |(2675878087/5000000000 : ℝ)|=(2675878087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991581399/5000000000 : ℝ)|^4515 ≤ (6169152786059/50000000000000 : ℝ)^3491
        have hw : |(-991581399/5000000000 : ℝ)|=(991581399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130437089/250000000 : ℝ)|^4515 ≤ (21555354585621/50000000000000 : ℝ)^3491
        have hw : |(130437089/250000000 : ℝ)|=(130437089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351756233/10000000000 : ℝ)*x 0 + (5217483539/10000000000 : ℝ)*x 1 + (-495790687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351756233/10000000000 : ℝ)^4515 ≤ (5568873234439/12500000000000 : ℝ)^3491 := by
    have hnat : (5351756233 : ℕ)^4515*12500000000000^3491 ≤ 5568873234439^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351756233 10000000000 5568873234439 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217483539/10000000000 : ℝ)^4515 ≤ (10777677236707/25000000000000 : ℝ)^3491 := by
    have hnat : (5217483539 : ℕ)^4515*25000000000000^3491 ≤ 10777677236707^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217483539 10000000000 10777677236707 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495790687/2500000000 : ℝ)^4515 ≤ (2467661033959/20000000000000 : ℝ)^3491 := by
    have hnat : (495790687 : ℕ)^4515*20000000000000^3491 ≤ 2467661033959^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495790687 2500000000 2467661033959 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351756233/10000000000 : ℝ), (5217483539/10000000000 : ℝ), (-495790687/2500000000 : ℝ)] ![(5568873234439/12500000000000 : ℝ), (10777677236707/25000000000000 : ℝ), (2467661033959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351756233/10000000000 : ℝ)|^4515 ≤ (5568873234439/12500000000000 : ℝ)^3491
        have hw : |(5351756233/10000000000 : ℝ)|=(5351756233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217483539/10000000000 : ℝ)|^4515 ≤ (10777677236707/25000000000000 : ℝ)^3491
        have hw : |(5217483539/10000000000 : ℝ)|=(5217483539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495790687/2500000000 : ℝ)|^4515 ≤ (2467661033959/20000000000000 : ℝ)^3491
        have hw : |(-495790687/2500000000 : ℝ)|=(495790687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271171279/10000000000 : ℝ)*x 0 + (4032590743/10000000000 : ℝ)*x 1 + (36173349/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271171279/10000000000 : ℝ)^4515 ≤ (3327951021103/10000000000000 : ℝ)^3491 := by
    have hnat : (4271171279 : ℕ)^4515*10000000000000^3491 ≤ 3327951021103^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271171279 10000000000 3327951021103 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032590743/10000000000 : ℝ)^4515 ≤ (15447629677697/50000000000000 : ℝ)^3491 := by
    have hnat : (4032590743 : ℕ)^4515*50000000000000^3491 ≤ 15447629677697^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032590743 10000000000 15447629677697 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36173349/80000000 : ℝ)^4515 ≤ (4478153803223/12500000000000 : ℝ)^3491 := by
    have hnat : (36173349 : ℕ)^4515*12500000000000^3491 ≤ 4478153803223^3491*80000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36173349 80000000 4478153803223 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271171279/10000000000 : ℝ), (4032590743/10000000000 : ℝ), (36173349/80000000 : ℝ)] ![(3327951021103/10000000000000 : ℝ), (15447629677697/50000000000000 : ℝ), (4478153803223/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271171279/10000000000 : ℝ)|^4515 ≤ (3327951021103/10000000000000 : ℝ)^3491
        have hw : |(4271171279/10000000000 : ℝ)|=(4271171279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032590743/10000000000 : ℝ)|^4515 ≤ (15447629677697/50000000000000 : ℝ)^3491
        have hw : |(4032590743/10000000000 : ℝ)|=(4032590743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36173349/80000000 : ℝ)|^4515 ≤ (4478153803223/12500000000000 : ℝ)^3491
        have hw : |(36173349/80000000 : ℝ)|=(36173349/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872488687/10000000000 : ℝ)*x 0 + (2609297957/5000000000 : ℝ)*x 1 + (1358125621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872488687/10000000000 : ℝ)^4515 ≤ (2863789341207/25000000000000 : ℝ)^3491 := by
    have hnat : (1872488687 : ℕ)^4515*25000000000000^3491 ≤ 2863789341207^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872488687 10000000000 2863789341207 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609297957/5000000000 : ℝ)^4515 ≤ (21561298308977/50000000000000 : ℝ)^3491 := by
    have hnat : (2609297957 : ℕ)^4515*50000000000000^3491 ≤ 21561298308977^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609297957 5000000000 21561298308977 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358125621/2500000000 : ℝ)^4515 ≤ (22711122998657/50000000000000 : ℝ)^3491 := by
    have hnat : (1358125621 : ℕ)^4515*50000000000000^3491 ≤ 22711122998657^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358125621 2500000000 22711122998657 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872488687/10000000000 : ℝ), (2609297957/5000000000 : ℝ), (1358125621/2500000000 : ℝ)] ![(2863789341207/25000000000000 : ℝ), (21561298308977/50000000000000 : ℝ), (22711122998657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872488687/10000000000 : ℝ)|^4515 ≤ (2863789341207/25000000000000 : ℝ)^3491
        have hw : |(-1872488687/10000000000 : ℝ)|=(1872488687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609297957/5000000000 : ℝ)|^4515 ≤ (21561298308977/50000000000000 : ℝ)^3491
        have hw : |(2609297957/5000000000 : ℝ)|=(2609297957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358125621/2500000000 : ℝ)|^4515 ≤ (22711122998657/50000000000000 : ℝ)^3491
        have hw : |(1358125621/2500000000 : ℝ)|=(1358125621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295042093/10000000000 : ℝ)*x 0 + (-884071977/5000000000 : ℝ)*x 1 + (21730013/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295042093/10000000000 : ℝ)^4515 ≤ (8788266484309/20000000000000 : ℝ)^3491 := by
    have hnat : (5295042093 : ℕ)^4515*20000000000000^3491 ≤ 8788266484309^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295042093 10000000000 8788266484309 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884071977/5000000000 : ℝ)^4515 ≤ (10636413280751/100000000000000 : ℝ)^3491 := by
    have hnat : (884071977 : ℕ)^4515*100000000000000^3491 ≤ 10636413280751^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884071977 5000000000 10636413280751 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21730013/40000000 : ℝ)^4515 ≤ (11355563570163/25000000000000 : ℝ)^3491 := by
    have hnat : (21730013 : ℕ)^4515*25000000000000^3491 ≤ 11355563570163^3491*40000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21730013 40000000 11355563570163 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295042093/10000000000 : ℝ), (-884071977/5000000000 : ℝ), (21730013/40000000 : ℝ)] ![(8788266484309/20000000000000 : ℝ), (10636413280751/100000000000000 : ℝ), (11355563570163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295042093/10000000000 : ℝ)|^4515 ≤ (8788266484309/20000000000000 : ℝ)^3491
        have hw : |(5295042093/10000000000 : ℝ)|=(5295042093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884071977/5000000000 : ℝ)|^4515 ≤ (10636413280751/100000000000000 : ℝ)^3491
        have hw : |(-884071977/5000000000 : ℝ)|=(884071977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21730013/40000000 : ℝ)|^4515 ≤ (11355563570163/25000000000000 : ℝ)^3491
        have hw : |(21730013/40000000 : ℝ)|=(21730013/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295042331/10000000000 : ℝ)*x 0 + (5432503243/10000000000 : ℝ)*x 1 + (-353628727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295042331/10000000000 : ℝ)^4515 ≤ (5492666871993/12500000000000 : ℝ)^3491 := by
    have hnat : (5295042331 : ℕ)^4515*12500000000000^3491 ≤ 5492666871993^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295042331 10000000000 5492666871993 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432503243/10000000000 : ℝ)^4515 ≤ (11355563551239/25000000000000 : ℝ)^3491 := by
    have hnat : (5432503243 : ℕ)^4515*25000000000000^3491 ≤ 11355563551239^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432503243 10000000000 11355563551239 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353628727/2000000000 : ℝ)^4515 ≤ (5318205399449/50000000000000 : ℝ)^3491 := by
    have hnat : (353628727 : ℕ)^4515*50000000000000^3491 ≤ 5318205399449^3491*2000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353628727 2000000000 5318205399449 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295042331/10000000000 : ℝ), (5432503243/10000000000 : ℝ), (-353628727/2000000000 : ℝ)] ![(5492666871993/12500000000000 : ℝ), (11355563551239/25000000000000 : ℝ), (5318205399449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295042331/10000000000 : ℝ)|^4515 ≤ (5492666871993/12500000000000 : ℝ)^3491
        have hw : |(5295042331/10000000000 : ℝ)|=(5295042331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432503243/10000000000 : ℝ)|^4515 ≤ (11355563551239/25000000000000 : ℝ)^3491
        have hw : |(5432503243/10000000000 : ℝ)|=(5432503243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353628727/2000000000 : ℝ)|^4515 ≤ (5318205399449/50000000000000 : ℝ)^3491
        have hw : |(-353628727/2000000000 : ℝ)|=(353628727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_s6_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271237969/10000000000 : ℝ)*x 0 + (4519151673/10000000000 : ℝ)*x 1 + (4035125371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271237969/10000000000 : ℝ)^4515 ≤ (3328018225789/10000000000000 : ℝ)^3491 := by
    have hnat : (4271237969 : ℕ)^4515*10000000000000^3491 ≤ 3328018225789^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271237969 10000000000 3328018225789 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519151673/10000000000 : ℝ)^4515 ≤ (17899720619763/50000000000000 : ℝ)^3491 := by
    have hnat : (4519151673 : ℕ)^4515*50000000000000^3491 ≤ 17899720619763^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519151673 10000000000 17899720619763 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035125371/10000000000 : ℝ)^4515 ≤ (7730094119091/25000000000000 : ℝ)^3491 := by
    have hnat : (4035125371 : ℕ)^4515*25000000000000^3491 ≤ 7730094119091^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035125371 10000000000 7730094119091 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271237969/10000000000 : ℝ), (4519151673/10000000000 : ℝ), (4035125371/10000000000 : ℝ)] ![(3328018225789/10000000000000 : ℝ), (17899720619763/50000000000000 : ℝ), (7730094119091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271237969/10000000000 : ℝ)|^4515 ≤ (3328018225789/10000000000000 : ℝ)^3491
        have hw : |(4271237969/10000000000 : ℝ)|=(4271237969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519151673/10000000000 : ℝ)|^4515 ≤ (17899720619763/50000000000000 : ℝ)^3491
        have hw : |(4519151673/10000000000 : ℝ)|=(4519151673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035125371/10000000000 : ℝ)|^4515 ≤ (7730094119091/25000000000000 : ℝ)^3491
        have hw : |(4035125371/10000000000 : ℝ)|=(4035125371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1363/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (10903/100000 : ℝ) ^ (4513/1024 : ℝ) ≤ (2865610920923983/50000000000000000000 : ℝ) := by
    have hpowers : (10903/100000 : ℝ)^4513 ≤ (2865610920923983/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10903 : ℕ)^4513*50000000000000000000^1024 ≤ 2865610920923983^1024*100000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10903 100000 2865610920923983 50000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10903/100000 : ℝ)) (X := (2865610920923983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4513/1024 : ℝ) ≤ (5375443581402363/20000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4513 ≤ (5375443581402363/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4513*20000000000000000000^1024 ≤ 5375443581402363^1024*50000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 5375443581402363 20000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (5375443581402363/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002865610920923983/25000000000000000000 : ℝ) ≤ (10000260071400387/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (25002865610920923983/25000000000000000000 : ℝ)^1024 ≤ (10000260071400387/10000000000000000 : ℝ)^4513 := by
      have hnat : (25002865610920923983 : ℕ)^1024*10000000000000000^4513 ≤ 10000260071400387^4513*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002865610920923983 25000000000000000000 10000260071400387 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000260071400387/10000000000000000 : ℝ)) (X := (25002865610920923983/25000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032608439748859781/100000000000000000000 : ℝ) ≤ (2000147958494317/2000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (100032608439748859781/100000000000000000000 : ℝ)^1024 ≤ (2000147958494317/2000000000000000 : ℝ)^4513 := by
      have hnat : (100032608439748859781 : ℕ)^1024*2000000000000000^4513 ≤ 2000147958494317^4513*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032608439748859781 100000000000000000000 2000147958494317 2000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000147958494317/2000000000000000 : ℝ)) (X := (100032608439748859781/100000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005375443581402363/10000000000000000000 : ℝ) ≤ (10001219513542783/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (10005375443581402363/10000000000000000000 : ℝ)^1024 ≤ (10001219513542783/10000000000000000 : ℝ)^4513 := by
      have hnat : (10005375443581402363 : ℕ)^1024*10000000000000000^4513 ≤ 10001219513542783^4513*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005375443581402363 10000000000000000000 10001219513542783 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001219513542783/10000000000000000 : ℝ)) (X := (10005375443581402363/10000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2865610920923983/50000000000000000000 : ℝ) ≤ ((9156146013852765697/9158000000000000000 : ℝ)+2*(239860535599/228950000000000 : ℝ)*(10903/100000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (9156146013852765697/9158000000000000000 : ℝ)+2*(239860535599/228950000000000 : ℝ)*(10903/100000 : ℝ)=(10000260071400387/10000000000000000 : ℝ) by norm_num, show 1+2*(2865610920923983/50000000000000000000 : ℝ)=(25002865610920923983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5375443581402363/20000000000000000000 : ℝ)+(2865610920923983/50000000000000000000 : ℝ) ≤ ((9156146013852765697/9158000000000000000 : ℝ)+(239860535599/228950000000000 : ℝ)*((7741/50000 : ℝ)+(10903/100000 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (9156146013852765697/9158000000000000000 : ℝ)+(239860535599/228950000000000 : ℝ)*((7741/50000 : ℝ)+(10903/100000 : ℝ))=(2000147958494317/2000000000000000 : ℝ) by norm_num, show 1+(5375443581402363/20000000000000000000 : ℝ)+(2865610920923983/50000000000000000000 : ℝ)=(100032608439748859781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5375443581402363/20000000000000000000 : ℝ) ≤ ((9156146013852765697/9158000000000000000 : ℝ)+2*(239860535599/228950000000000 : ℝ)*(7741/50000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (9156146013852765697/9158000000000000000 : ℝ)+2*(239860535599/228950000000000 : ℝ)*(7741/50000 : ℝ)=(10001219513542783/10000000000000000 : ℝ) by norm_num, show 1+2*(5375443581402363/20000000000000000000 : ℝ)=(10005375443581402363/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9156146013852765697/9158000000000000000 : ℝ)*(X 1 0+X 2 0)+(239860535599/228950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (10903/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (9156146013852765697/9158000000000000000 : ℝ)) (alpha := (239860535599/228950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9156146013852765697/9158000000000000000 : ℝ)*(X 0 1+X 2 1)+(239860535599/228950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (10903/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (9156146013852765697/9158000000000000000 : ℝ)) (alpha := (239860535599/228950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9156146013852765697/9158000000000000000 : ℝ)*(X 0 2+X 1 2)+(239860535599/228950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (10903/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (9156146013852765697/9158000000000000000 : ℝ)) (alpha := (239860535599/228950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1872460131/10000000000 : ℝ)*X 0 0+(5433622651/10000000000 : ℝ)*X 0 1+(2608741771/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675878087/5000000000 : ℝ)*X 1 0+(-991581399/5000000000 : ℝ)*X 1 1+(130437089/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351756233/10000000000 : ℝ)*X 2 0+(5217483539/10000000000 : ℝ)*X 2 1+(-495790687/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4271171279/10000000000 : ℝ)*X 0 0+(4032590743/10000000000 : ℝ)*X 0 1+(36173349/80000000 : ℝ)*X 0 2+(4271171279/10000000000 : ℝ)*X 1 0+(4032590743/10000000000 : ℝ)*X 1 1+(36173349/80000000 : ℝ)*X 1 2+(4271171279/10000000000 : ℝ)*X 2 0+(4032590743/10000000000 : ℝ)*X 2 1+(36173349/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1872488687/10000000000 : ℝ)*X 0 0+(2609297957/5000000000 : ℝ)*X 0 1+(1358125621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295042093/10000000000 : ℝ)*X 1 0+(-884071977/5000000000 : ℝ)*X 1 1+(21730013/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295042331/10000000000 : ℝ)*X 2 0+(5432503243/10000000000 : ℝ)*X 2 1+(-353628727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271237969/10000000000 : ℝ)*X 0 0+(4519151673/10000000000 : ℝ)*X 0 1+(4035125371/10000000000 : ℝ)*X 0 2+(4271237969/10000000000 : ℝ)*X 1 0+(4519151673/10000000000 : ℝ)*X 1 1+(4035125371/10000000000 : ℝ)*X 1 2+(4271237969/10000000000 : ℝ)*X 2 0+(4519151673/10000000000 : ℝ)*X 2 1+(4035125371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2192345512782285114248364291/228950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (346484393/20000000000000 : ℝ)*(base19) + (849536811/50000000000000 : ℝ)*(base23) + (4514479/10000000000000 : ℝ)*(lower2) + (193694031/100000000000000 : ℝ)*(upper3) + (94348829/50000000000000 : ℝ)*(upper5) + (1667849692516933/50000000000000 : ℝ)*(major0) + (1667849692516933/50000000000000 : ℝ)*(major1) + (1667849692516933/50000000000000 : ℝ)*(major2) + (4626678606866209/100000000000000 : ℝ)*(sp0) + (289169174161599/6250000000000 : ℝ)*(sp1) + (2313353409966963/50000000000000 : ℝ)*(sp2) + (2044676740693839/100000000000000 : ℝ)*(sp3) + (29912141339/100000000000000 : ℝ)*(sp4) + (13191177931/100000000000000 : ℝ)*(sp7) + (204468993187177/10000000000000 : ℝ)*(f.failure) + (1156677129751887/25000000000000 : ℝ)*(f.sum) + (7843694307313/1430937500000000000000000000 : ℝ)*base65 + (8353148354943227301/457900000000000000000000000000000 : ℝ)*base67 + (1645161864141727301/457900000000000000000000000000000 : ℝ)*base69 + (1994264500864327301/457900000000000000000000000000000 : ℝ)*base71 + (25214599222851/2861875000000000000000000000 : ℝ)*base73 + (4610989008022327301/457900000000000000000000000000000 : ℝ)*base75 + (3108213792342527301/457900000000000000000000000000000 : ℝ)*base77 + (4722983454742127301/457900000000000000000000000000000 : ℝ)*base79 + (22777239059773/5723750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (767363/50000000000000000000 : ℝ)*base90 + (767363/50000000000000000000 : ℝ)*base92 + (767363/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (925640544678035481502645959/228950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123897779/25000000000000 : ℝ)*(base15) + (16864793/50000000000000 : ℝ)*(lower1) + (180660167/100000000000000 : ℝ)*(lower2) + (55140103/100000000000000 : ℝ)*(upper3) + (129112169/50000000000000 : ℝ)*(lower4) + (34724859/100000000000000 : ℝ)*(upper5) + (1685233050926451/50000000000000 : ℝ)*(major0) + (1685233050926451/50000000000000 : ℝ)*(major1) + (1685233050926451/50000000000000 : ℝ)*(major2) + (7819247033/100000000000000 : ℝ)*(sp2) + (934986223441437/20000000000000 : ℝ)*(sp4) + (4674930621616069/100000000000000 : ℝ)*(sp5) + (584365412245019/12500000000000 : ℝ)*(sp6) + (516500237933143/25000000000000 : ℝ)*(sp7) + (516500237933143/25000000000000 : ℝ)*(f.failure) + (934986223441437/20000000000000 : ℝ)*(f.sum) + (568723994239/22895000000000000000000000000 : ℝ)*base66 + (265752826085311347/457900000000000000000000000000000 : ℝ)*base67 + (2094286404407911347/457900000000000000000000000000000 : ℝ)*base69 + (3473496872212788653/457900000000000000000000000000000 : ℝ)*base72 + (22862643760123/11447500000000000000000000000 : ℝ)*base73 + (3266704228898911347/457900000000000000000000000000000 : ℝ)*base75 + (2948317747173611347/457900000000000000000000000000000 : ℝ)*base77 + (807757381765388653/457900000000000000000000000000000 : ℝ)*base80 + (58947501035391/5723750000000000000000000000 : ℝ)*base82 + (778717/125000000000000000000 : ℝ)*base90 + (778717/125000000000000000000 : ℝ)*base92 + (778717/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1509_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1363/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1509_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1509_box_0 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414574039/2500000000 : ℝ)*x 0 + (1350789117/2500000000 : ℝ)*x 1 + (5403156091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414574039/2500000000 : ℝ)^4515 ≤ (978968991057/10000000000000 : ℝ)^3491 := by
    have hnat : (414574039 : ℕ)^4515*10000000000000^3491 ≤ 978968991057^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414574039 2500000000 978968991057 10000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350789117/2500000000 : ℝ)^4515 ≤ (45105157070379/100000000000000 : ℝ)^3491 := by
    have hnat : (1350789117 : ℕ)^4515*100000000000000^3491 ≤ 45105157070379^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350789117 2500000000 45105157070379 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403156091/10000000000 : ℝ)^4515 ≤ (22552576500033/50000000000000 : ℝ)^3491 := by
    have hnat : (5403156091 : ℕ)^4515*50000000000000^3491 ≤ 22552576500033^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403156091 10000000000 22552576500033 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414574039/2500000000 : ℝ), (1350789117/2500000000 : ℝ), (5403156091/10000000000 : ℝ)] ![(978968991057/10000000000000 : ℝ), (45105157070379/100000000000000 : ℝ), (22552576500033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414574039/2500000000 : ℝ)|^4515 ≤ (978968991057/10000000000000 : ℝ)^3491
        have hw : |(-414574039/2500000000 : ℝ)|=(414574039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350789117/2500000000 : ℝ)|^4515 ≤ (45105157070379/100000000000000 : ℝ)^3491
        have hw : |(1350789117/2500000000 : ℝ)|=(1350789117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403156091/10000000000 : ℝ)|^4515 ≤ (22552576500033/50000000000000 : ℝ)^3491
        have hw : |(5403156091/10000000000 : ℝ)|=(5403156091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_1 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635368563/5000000000 : ℝ)*x 0 + (-92098027/500000000 : ℝ)*x 1 + (5403156259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635368563/5000000000 : ℝ)^4515 ≤ (43680648669667/100000000000000 : ℝ)^3491 := by
    have hnat : (2635368563 : ℕ)^4515*100000000000000^3491 ≤ 43680648669667^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635368563 5000000000 43680648669667 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92098027/500000000 : ℝ)^4515 ≤ (11214196514091/100000000000000 : ℝ)^3491 := by
    have hnat : (92098027 : ℕ)^4515*100000000000000^3491 ≤ 11214196514091^3491*500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92098027 500000000 11214196514091 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403156259/10000000000 : ℝ)^4515 ≤ (11276288703473/25000000000000 : ℝ)^3491 := by
    have hnat : (5403156259 : ℕ)^4515*25000000000000^3491 ≤ 11276288703473^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403156259 10000000000 11276288703473 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635368563/5000000000 : ℝ), (-92098027/500000000 : ℝ), (5403156259/10000000000 : ℝ)] ![(43680648669667/100000000000000 : ℝ), (11214196514091/100000000000000 : ℝ), (11276288703473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635368563/5000000000 : ℝ)|^4515 ≤ (43680648669667/100000000000000 : ℝ)^3491
        have hw : |(2635368563/5000000000 : ℝ)|=(2635368563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92098027/500000000 : ℝ)|^4515 ≤ (11214196514091/100000000000000 : ℝ)^3491
        have hw : |(-92098027/500000000 : ℝ)|=(92098027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403156259/10000000000 : ℝ)|^4515 ≤ (11276288703473/25000000000000 : ℝ)^3491
        have hw : |(5403156259/10000000000 : ℝ)|=(5403156259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_2 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635368389/5000000000 : ℝ)*x 0 + (5403156523/10000000000 : ℝ)*x 1 + (-36839213/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635368389/5000000000 : ℝ)^4515 ≤ (43680644939701/100000000000000 : ℝ)^3491 := by
    have hnat : (2635368389 : ℕ)^4515*100000000000000^3491 ≤ 43680644939701^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635368389 5000000000 43680644939701 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403156523/10000000000 : ℝ)^4515 ≤ (704768088503/1562500000000 : ℝ)^3491 := by
    have hnat : (5403156523 : ℕ)^4515*1562500000000^3491 ≤ 704768088503^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403156523 10000000000 704768088503 1562500000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36839213/200000000 : ℝ)^4515 ≤ (1401774672529/12500000000000 : ℝ)^3491 := by
    have hnat : (36839213 : ℕ)^4515*12500000000000^3491 ≤ 1401774672529^3491*200000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36839213 200000000 1401774672529 12500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635368389/5000000000 : ℝ), (5403156523/10000000000 : ℝ), (-36839213/200000000 : ℝ)] ![(43680644939701/100000000000000 : ℝ), (704768088503/1562500000000 : ℝ), (1401774672529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635368389/5000000000 : ℝ)|^4515 ≤ (43680644939701/100000000000000 : ℝ)^3491
        have hw : |(2635368389/5000000000 : ℝ)|=(2635368389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403156523/10000000000 : ℝ)|^4515 ≤ (704768088503/1562500000000 : ℝ)^3491
        have hw : |(5403156523/10000000000 : ℝ)|=(5403156523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36839213/200000000 : ℝ)|^4515 ≤ (1401774672529/12500000000000 : ℝ)^3491
        have hw : |(-36839213/200000000 : ℝ)|=(36839213/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_3 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (559296347/1250000000 : ℝ)*x 0 + (4176573409/10000000000 : ℝ)*x 1 + (1044143231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559296347/1250000000 : ℝ)^4515 ≤ (35341313147433/100000000000000 : ℝ)^3491 := by
    have hnat : (559296347 : ℕ)^4515*100000000000000^3491 ≤ 35341313147433^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559296347 1250000000 35341313147433 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4176573409/10000000000 : ℝ)^4515 ≤ (1010292057733/3125000000000 : ℝ)^3491 := by
    have hnat : (4176573409 : ℕ)^4515*3125000000000^3491 ≤ 1010292057733^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176573409 10000000000 1010292057733 3125000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044143231/2500000000 : ℝ)^4515 ≤ (808233524801/2500000000000 : ℝ)^3491 := by
    have hnat : (1044143231 : ℕ)^4515*2500000000000^3491 ≤ 808233524801^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044143231 2500000000 808233524801 2500000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(559296347/1250000000 : ℝ), (4176573409/10000000000 : ℝ), (1044143231/2500000000 : ℝ)] ![(35341313147433/100000000000000 : ℝ), (1010292057733/3125000000000 : ℝ), (808233524801/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(559296347/1250000000 : ℝ)|^4515 ≤ (35341313147433/100000000000000 : ℝ)^3491
        have hw : |(559296347/1250000000 : ℝ)|=(559296347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4176573409/10000000000 : ℝ)|^4515 ≤ (1010292057733/3125000000000 : ℝ)^3491
        have hw : |(4176573409/10000000000 : ℝ)|=(4176573409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044143231/2500000000 : ℝ)|^4515 ≤ (808233524801/2500000000000 : ℝ)^3491
        have hw : |(1044143231/2500000000 : ℝ)|=(1044143231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_4 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046033099/5000000000 : ℝ)*x 0 + (1310881643/2500000000 : ℝ)*x 1 + (5243526641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046033099/5000000000 : ℝ)^4515 ≤ (13221561102097/100000000000000 : ℝ)^3491 := by
    have hnat : (1046033099 : ℕ)^4515*100000000000000^3491 ≤ 13221561102097^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046033099 5000000000 13221561102097 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310881643/2500000000 : ℝ)^4515 ≤ (43389219071527/100000000000000 : ℝ)^3491 := by
    have hnat : (1310881643 : ℕ)^4515*100000000000000^3491 ≤ 43389219071527^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310881643 2500000000 43389219071527 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243526641/10000000000 : ℝ)^4515 ≤ (43389219809967/100000000000000 : ℝ)^3491 := by
    have hnat : (5243526641 : ℕ)^4515*100000000000000^3491 ≤ 43389219809967^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243526641 10000000000 43389219809967 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046033099/5000000000 : ℝ), (1310881643/2500000000 : ℝ), (5243526641/10000000000 : ℝ)] ![(13221561102097/100000000000000 : ℝ), (43389219071527/100000000000000 : ℝ), (43389219809967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046033099/5000000000 : ℝ)|^4515 ≤ (13221561102097/100000000000000 : ℝ)^3491
        have hw : |(-1046033099/5000000000 : ℝ)|=(1046033099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310881643/2500000000 : ℝ)|^4515 ≤ (43389219071527/100000000000000 : ℝ)^3491
        have hw : |(1310881643/2500000000 : ℝ)|=(1310881643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243526641/10000000000 : ℝ)|^4515 ≤ (43389219809967/100000000000000 : ℝ)^3491
        have hw : |(5243526641/10000000000 : ℝ)|=(5243526641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_5 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345475143/2500000000 : ℝ)*x 0 + (-1907758557/10000000000 : ℝ)*x 1 + (2621763293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345475143/2500000000 : ℝ)^4515 ≤ (22437899216883/50000000000000 : ℝ)^3491 := by
    have hnat : (1345475143 : ℕ)^4515*50000000000000^3491 ≤ 22437899216883^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345475143 2500000000 22437899216883 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1907758557/10000000000 : ℝ)^4515 ≤ (11734982322571/100000000000000 : ℝ)^3491 := by
    have hnat : (1907758557 : ℕ)^4515*100000000000000^3491 ≤ 11734982322571^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907758557 10000000000 11734982322571 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621763293/5000000000 : ℝ)^4515 ≤ (10847304805339/25000000000000 : ℝ)^3491 := by
    have hnat : (2621763293 : ℕ)^4515*25000000000000^3491 ≤ 10847304805339^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621763293 5000000000 10847304805339 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345475143/2500000000 : ℝ), (-1907758557/10000000000 : ℝ), (2621763293/5000000000 : ℝ)] ![(22437899216883/50000000000000 : ℝ), (11734982322571/100000000000000 : ℝ), (10847304805339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345475143/2500000000 : ℝ)|^4515 ≤ (22437899216883/50000000000000 : ℝ)^3491
        have hw : |(1345475143/2500000000 : ℝ)|=(1345475143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1907758557/10000000000 : ℝ)|^4515 ≤ (11734982322571/100000000000000 : ℝ)^3491
        have hw : |(-1907758557/10000000000 : ℝ)|=(1907758557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621763293/5000000000 : ℝ)|^4515 ≤ (10847304805339/25000000000000 : ℝ)^3491
        have hw : |(2621763293/5000000000 : ℝ)|=(2621763293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_6 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381900511/10000000000 : ℝ)*x 0 + (2621763343/5000000000 : ℝ)*x 1 + (-1907758507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381900511/10000000000 : ℝ)^4515 ≤ (8975159555187/20000000000000 : ℝ)^3491 := by
    have hnat : (5381900511 : ℕ)^4515*20000000000000^3491 ≤ 8975159555187^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381900511 10000000000 8975159555187 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621763343/5000000000 : ℝ)^4515 ≤ (43389220291559/100000000000000 : ℝ)^3491 := by
    have hnat : (2621763343 : ℕ)^4515*100000000000000^3491 ≤ 43389220291559^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621763343 5000000000 43389220291559 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1907758507/10000000000 : ℝ)^4515 ≤ (2933745481199/25000000000000 : ℝ)^3491 := by
    have hnat : (1907758507 : ℕ)^4515*25000000000000^3491 ≤ 2933745481199^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907758507 10000000000 2933745481199 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381900511/10000000000 : ℝ), (2621763343/5000000000 : ℝ), (-1907758507/10000000000 : ℝ)] ![(8975159555187/20000000000000 : ℝ), (43389220291559/100000000000000 : ℝ), (2933745481199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381900511/10000000000 : ℝ)|^4515 ≤ (8975159555187/20000000000000 : ℝ)^3491
        have hw : |(5381900511/10000000000 : ℝ)|=(5381900511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621763343/5000000000 : ℝ)|^4515 ≤ (43389220291559/100000000000000 : ℝ)^3491
        have hw : |(2621763343/5000000000 : ℝ)|=(2621763343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1907758507/10000000000 : ℝ)|^4515 ≤ (2933745481199/25000000000000 : ℝ)^3491
        have hw : |(-1907758507/10000000000 : ℝ)|=(1907758507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_7 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4065567529/10000000000 : ℝ)*x 0 + (4380840103/10000000000 : ℝ)*x 1 + (438084011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4065567529/10000000000 : ℝ)^4515 ≤ (30490631607/97656250000 : ℝ)^3491 := by
    have hnat : (4065567529 : ℕ)^4515*97656250000^3491 ≤ 30490631607^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4065567529 10000000000 30490631607 97656250000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4380840103/10000000000 : ℝ)^4515 ≤ (134331236611/390625000000 : ℝ)^3491 := by
    have hnat : (4380840103 : ℕ)^4515*390625000000^3491 ≤ 134331236611^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380840103 10000000000 134331236611 390625000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438084011/1000000000 : ℝ)^4515 ≤ (34388796643483/100000000000000 : ℝ)^3491 := by
    have hnat : (438084011 : ℕ)^4515*100000000000000^3491 ≤ 34388796643483^3491*1000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438084011 1000000000 34388796643483 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4065567529/10000000000 : ℝ), (4380840103/10000000000 : ℝ), (438084011/1000000000 : ℝ)] ![(30490631607/97656250000 : ℝ), (134331236611/390625000000 : ℝ), (34388796643483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4065567529/10000000000 : ℝ)|^4515 ≤ (30490631607/97656250000 : ℝ)^3491
        have hw : |(4065567529/10000000000 : ℝ)|=(4065567529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4380840103/10000000000 : ℝ)|^4515 ≤ (134331236611/390625000000 : ℝ)^3491
        have hw : |(4380840103/10000000000 : ℝ)|=(4380840103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438084011/1000000000 : ℝ)|^4515 ≤ (34388796643483/100000000000000 : ℝ)^3491
        have hw : |(438084011/1000000000 : ℝ)|=(438084011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_8 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-500103973/2500000000 : ℝ)*x 0 + (5131726773/10000000000 : ℝ)*x 1 + (2711809111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500103973/2500000000 : ℝ)^4515 ≤ (6238654369981/50000000000000 : ℝ)^3491 := by
    have hnat : (500103973 : ℕ)^4515*50000000000000^3491 ≤ 6238654369981^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500103973 2500000000 6238654369981 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131726773/10000000000 : ℝ)^4515 ≤ (10549123611093/25000000000000 : ℝ)^3491 := by
    have hnat : (5131726773 : ℕ)^4515*25000000000000^3491 ≤ 10549123611093^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131726773 10000000000 10549123611093 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711809111/5000000000 : ℝ)^4515 ≤ (45326196805219/100000000000000 : ℝ)^3491 := by
    have hnat : (2711809111 : ℕ)^4515*100000000000000^3491 ≤ 45326196805219^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711809111 5000000000 45326196805219 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-500103973/2500000000 : ℝ), (5131726773/10000000000 : ℝ), (2711809111/5000000000 : ℝ)] ![(6238654369981/50000000000000 : ℝ), (10549123611093/25000000000000 : ℝ), (45326196805219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-500103973/2500000000 : ℝ)|^4515 ≤ (6238654369981/50000000000000 : ℝ)^3491
        have hw : |(-500103973/2500000000 : ℝ)|=(500103973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131726773/10000000000 : ℝ)|^4515 ≤ (10549123611093/25000000000000 : ℝ)^3491
        have hw : |(5131726773/10000000000 : ℝ)|=(5131726773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711809111/5000000000 : ℝ)|^4515 ≤ (45326196805219/100000000000000 : ℝ)^3491
        have hw : |(2711809111/5000000000 : ℝ)|=(2711809111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_9 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256481583/10000000000 : ℝ)*x 0 + (-229159937/1250000000 : ℝ)*x 1 + (5423618197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256481583/10000000000 : ℝ)^4515 ≤ (8705582846011/20000000000000 : ℝ)^3491 := by
    have hnat : (5256481583 : ℕ)^4515*20000000000000^3491 ≤ 8705582846011^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256481583 10000000000 8705582846011 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229159937/1250000000 : ℝ)^4515 ≤ (2229177844191/20000000000000 : ℝ)^3491 := by
    have hnat : (229159937 : ℕ)^4515*20000000000000^3491 ≤ 2229177844191^3491*1250000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229159937 1250000000 2229177844191 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423618197/10000000000 : ℝ)^4515 ≤ (9065239307001/20000000000000 : ℝ)^3491 := by
    have hnat : (5423618197 : ℕ)^4515*20000000000000^3491 ≤ 9065239307001^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423618197 10000000000 9065239307001 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256481583/10000000000 : ℝ), (-229159937/1250000000 : ℝ), (5423618197/10000000000 : ℝ)] ![(8705582846011/20000000000000 : ℝ), (2229177844191/20000000000000 : ℝ), (9065239307001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256481583/10000000000 : ℝ)|^4515 ≤ (8705582846011/20000000000000 : ℝ)^3491
        have hw : |(5256481583/10000000000 : ℝ)|=(5256481583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-229159937/1250000000 : ℝ)|^4515 ≤ (2229177844191/20000000000000 : ℝ)^3491
        have hw : |(-229159937/1250000000 : ℝ)|=(229159937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423618197/10000000000 : ℝ)|^4515 ≤ (9065239307001/20000000000000 : ℝ)^3491
        have hw : |(5423618197/10000000000 : ℝ)|=(5423618197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_10 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314120381/2500000000 : ℝ)*x 0 + (5423618403/10000000000 : ℝ)*x 1 + (-1833279293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314120381/2500000000 : ℝ)^4515 ≤ (21763956799089/50000000000000 : ℝ)^3491 := by
    have hnat : (1314120381 : ℕ)^4515*50000000000000^3491 ≤ 21763956799089^3491*2500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314120381 2500000000 21763956799089 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423618403/10000000000 : ℝ)^4515 ≤ (45326198761569/100000000000000 : ℝ)^3491 := by
    have hnat : (5423618403 : ℕ)^4515*100000000000000^3491 ≤ 45326198761569^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423618403 10000000000 45326198761569 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833279293/10000000000 : ℝ)^4515 ≤ (2229177524949/20000000000000 : ℝ)^3491 := by
    have hnat : (1833279293 : ℕ)^4515*20000000000000^3491 ≤ 2229177524949^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833279293 10000000000 2229177524949 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314120381/2500000000 : ℝ), (5423618403/10000000000 : ℝ), (-1833279293/10000000000 : ℝ)] ![(21763956799089/50000000000000 : ℝ), (45326198761569/100000000000000 : ℝ), (2229177524949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314120381/2500000000 : ℝ)|^4515 ≤ (21763956799089/50000000000000 : ℝ)^3491
        have hw : |(1314120381/2500000000 : ℝ)|=(1314120381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423618403/10000000000 : ℝ)|^4515 ≤ (45326198761569/100000000000000 : ℝ)^3491
        have hw : |(5423618403/10000000000 : ℝ)|=(5423618403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833279293/10000000000 : ℝ)|^4515 ≤ (2229177524949/20000000000000 : ℝ)^3491
        have hw : |(-1833279293/10000000000 : ℝ)|=(1833279293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_11 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4525621139/10000000000 : ℝ)*x 0 + (2075178559/5000000000 : ℝ)*x 1 + (415035697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4525621139/10000000000 : ℝ)^4515 ≤ (17932868580733/50000000000000 : ℝ)^3491 := by
    have hnat : (4525621139 : ℕ)^4515*50000000000000^3491 ≤ 17932868580733^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525621139 10000000000 17932868580733 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075178559/5000000000 : ℝ)^4515 ≤ (16033566078251/50000000000000 : ℝ)^3491 := by
    have hnat : (2075178559 : ℕ)^4515*50000000000000^3491 ≤ 16033566078251^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075178559 5000000000 16033566078251 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415035697/1000000000 : ℝ)^4515 ≤ (32067130677583/100000000000000 : ℝ)^3491 := by
    have hnat : (415035697 : ℕ)^4515*100000000000000^3491 ≤ 32067130677583^3491*1000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415035697 1000000000 32067130677583 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4525621139/10000000000 : ℝ), (2075178559/5000000000 : ℝ), (415035697/1000000000 : ℝ)] ![(17932868580733/50000000000000 : ℝ), (16033566078251/50000000000000 : ℝ), (32067130677583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4525621139/10000000000 : ℝ)|^4515 ≤ (17932868580733/50000000000000 : ℝ)^3491
        have hw : |(4525621139/10000000000 : ℝ)|=(4525621139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075178559/5000000000 : ℝ)|^4515 ≤ (16033566078251/50000000000000 : ℝ)^3491
        have hw : |(2075178559/5000000000 : ℝ)|=(2075178559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415035697/1000000000 : ℝ)|^4515 ≤ (32067130677583/100000000000000 : ℝ)^3491
        have hw : |(415035697/1000000000 : ℝ)|=(415035697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_12 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1749912591/10000000000 : ℝ)*x 0 + (5511352093/10000000000 : ℝ)*x 1 + (5228502469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1749912591/10000000000 : ℝ)^4515 ≤ (2098957275003/20000000000000 : ℝ)^3491 := by
    have hnat : (1749912591 : ℕ)^4515*20000000000000^3491 ≤ 2098957275003^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749912591 10000000000 2098957275003 20000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511352093/10000000000 : ℝ)^4515 ≤ (11569178841143/25000000000000 : ℝ)^3491 := by
    have hnat : (5511352093 : ℕ)^4515*25000000000000^3491 ≤ 11569178841143^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511352093 10000000000 11569178841143 25000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228502469/10000000000 : ℝ)^4515 ≤ (21614249123063/50000000000000 : ℝ)^3491 := by
    have hnat : (5228502469 : ℕ)^4515*50000000000000^3491 ≤ 21614249123063^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228502469 10000000000 21614249123063 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1749912591/10000000000 : ℝ), (5511352093/10000000000 : ℝ), (5228502469/10000000000 : ℝ)] ![(2098957275003/20000000000000 : ℝ), (11569178841143/25000000000000 : ℝ), (21614249123063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1749912591/10000000000 : ℝ)|^4515 ≤ (2098957275003/20000000000000 : ℝ)^3491
        have hw : |(-1749912591/10000000000 : ℝ)|=(1749912591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511352093/10000000000 : ℝ)|^4515 ≤ (11569178841143/25000000000000 : ℝ)^3491
        have hw : |(5511352093/10000000000 : ℝ)|=(5511352093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228502469/10000000000 : ℝ)|^4515 ≤ (21614249123063/50000000000000 : ℝ)^3491
        have hw : |(5228502469/10000000000 : ℝ)|=(5228502469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_13 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696181079/5000000000 : ℝ)*x 0 + (-1913772529/10000000000 : ℝ)*x 1 + (163390713/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696181079/5000000000 : ℝ)^4515 ≤ (44988649506739/100000000000000 : ℝ)^3491 := by
    have hnat : (2696181079 : ℕ)^4515*100000000000000^3491 ≤ 44988649506739^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696181079 5000000000 44988649506739 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913772529/10000000000 : ℝ)^4515 ≤ (11782848520471/100000000000000 : ℝ)^3491 := by
    have hnat : (1913772529 : ℕ)^4515*100000000000000^3491 ≤ 11782848520471^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913772529 10000000000 11782848520471 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163390713/312500000 : ℝ)^4515 ≤ (43228501956607/100000000000000 : ℝ)^3491 := by
    have hnat : (163390713 : ℕ)^4515*100000000000000^3491 ≤ 43228501956607^3491*312500000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163390713 312500000 43228501956607 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696181079/5000000000 : ℝ), (-1913772529/10000000000 : ℝ), (163390713/312500000 : ℝ)] ![(44988649506739/100000000000000 : ℝ), (11782848520471/100000000000000 : ℝ), (43228501956607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696181079/5000000000 : ℝ)|^4515 ≤ (44988649506739/100000000000000 : ℝ)^3491
        have hw : |(2696181079/5000000000 : ℝ)|=(2696181079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1913772529/10000000000 : ℝ)|^4515 ≤ (11782848520471/100000000000000 : ℝ)^3491
        have hw : |(-1913772529/10000000000 : ℝ)|=(1913772529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163390713/312500000 : ℝ)|^4515 ≤ (43228501956607/100000000000000 : ℝ)^3491
        have hw : |(163390713/312500000 : ℝ)|=(163390713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_14 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392362287/10000000000 : ℝ)*x 0 + (5228502737/10000000000 : ℝ)*x 1 + (-1913772461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392362287/10000000000 : ℝ)^4515 ≤ (44988650898683/100000000000000 : ℝ)^3491 := by
    have hnat : (5392362287 : ℕ)^4515*100000000000000^3491 ≤ 44988650898683^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392362287 10000000000 44988650898683 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228502737/10000000000 : ℝ)^4515 ≤ (43228501111857/100000000000000 : ℝ)^3491 := by
    have hnat : (5228502737 : ℕ)^4515*100000000000000^3491 ≤ 43228501111857^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228502737 10000000000 43228501111857 100000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913772461/10000000000 : ℝ)^4515 ≤ (5891423989499/50000000000000 : ℝ)^3491 := by
    have hnat : (1913772461 : ℕ)^4515*50000000000000^3491 ≤ 5891423989499^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913772461 10000000000 5891423989499 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392362287/10000000000 : ℝ), (5228502737/10000000000 : ℝ), (-1913772461/10000000000 : ℝ)] ![(44988650898683/100000000000000 : ℝ), (43228501111857/100000000000000 : ℝ), (5891423989499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392362287/10000000000 : ℝ)|^4515 ≤ (44988650898683/100000000000000 : ℝ)^3491
        have hw : |(5392362287/10000000000 : ℝ)|=(5392362287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228502737/10000000000 : ℝ)|^4515 ≤ (43228501111857/100000000000000 : ℝ)^3491
        have hw : |(5228502737/10000000000 : ℝ)|=(5228502737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1913772461/10000000000 : ℝ)|^4515 ≤ (5891423989499/50000000000000 : ℝ)^3491
        have hw : |(-1913772461/10000000000 : ℝ)|=(1913772461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1509_box_15 (p : ℝ) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2013115231/5000000000 : ℝ)*x 0 + (4400043487/10000000000 : ℝ)*x 1 + (220002099/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013115231/5000000000 : ℝ)^4515 ≤ (1233290079161/4000000000000 : ℝ)^3491 := by
    have hnat : (2013115231 : ℕ)^4515*4000000000000^3491 ≤ 1233290079161^3491*5000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013115231 5000000000 1233290079161 4000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4400043487/10000000000 : ℝ)^4515 ≤ (17291940830891/50000000000000 : ℝ)^3491 := by
    have hnat : (4400043487 : ℕ)^4515*50000000000000^3491 ≤ 17291940830891^3491*10000000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400043487 10000000000 17291940830891 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220002099/500000000 : ℝ)^4515 ≤ (17291933171259/50000000000000 : ℝ)^3491 := by
    have hnat : (220002099 : ℕ)^4515*50000000000000^3491 ≤ 17291933171259^3491*500000000^4515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220002099 500000000 17291933171259 50000000000000 4515 3491 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4515/1024 : ℝ)) 4515 3491 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2013115231/5000000000 : ℝ), (4400043487/10000000000 : ℝ), (220002099/500000000 : ℝ)] ![(1233290079161/4000000000000 : ℝ), (17291940830891/50000000000000 : ℝ), (17291933171259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2013115231/5000000000 : ℝ)|^4515 ≤ (1233290079161/4000000000000 : ℝ)^3491
        have hw : |(2013115231/5000000000 : ℝ)|=(2013115231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4400043487/10000000000 : ℝ)|^4515 ≤ (17291940830891/50000000000000 : ℝ)^3491
        have hw : |(4400043487/10000000000 : ℝ)|=(4400043487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220002099/500000000 : ℝ)|^4515 ≤ (17291933171259/50000000000000 : ℝ)^3491
        have hw : |(220002099/500000000 : ℝ)|=(220002099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1509_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1363/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(12747/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29307/50000 : ℝ) ∧ (80287/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85983/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1363/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1363/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1363/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1363/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1363/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1363/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1363/12500 : ℝ) ^ (4513/1024 : ℝ) ≤ (5733538886712601/100000000000000000000 : ℝ) := by
    have hpowers : (1363/12500 : ℝ)^4513 ≤ (5733538886712601/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1363 : ℕ)^4513*100000000000000000000^1024 ≤ 5733538886712601^1024*12500^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1363 12500 5733538886712601 100000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1363/12500 : ℝ)) (X := (5733538886712601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4513/1024 : ℝ) ≤ (5373913534187747/20000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4513 ≤ (5373913534187747/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4513*20000000000000000000^1024 ≤ 5373913534187747^1024*100000^4513 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 5373913534187747 20000000000000000000 4513 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (5373913534187747/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005733538886712601/50000000000000000000 : ℝ) ≤ (2000052035307719/2000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (50005733538886712601/50000000000000000000 : ℝ)^1024 ≤ (2000052035307719/2000000000000000 : ℝ)^4513 := by
      have hnat : (50005733538886712601 : ℕ)^1024*2000000000000000^4513 ≤ 2000052035307719^4513*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005733538886712601 50000000000000000000 2000052035307719 2000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000052035307719/2000000000000000 : ℝ)) (X := (50005733538886712601/50000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504075388319706417/12500000000000000000 : ℝ) ≤ (312523114734123/312500000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (12504075388319706417/12500000000000000000 : ℝ)^1024 ≤ (312523114734123/312500000000000 : ℝ)^4513 := by
      have hnat : (12504075388319706417 : ℕ)^1024*312500000000000^4513 ≤ 312523114734123^4513*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504075388319706417 12500000000000000000 312523114734123 312500000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312523114734123/312500000000000 : ℝ)) (X := (12504075388319706417/12500000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005373913534187747/10000000000000000000 : ℝ) ≤ (10001219166445277/10000000000000000 : ℝ) ^ (4513/1024 : ℝ) := by
    have hpowers : (10005373913534187747/10000000000000000000 : ℝ)^1024 ≤ (10001219166445277/10000000000000000 : ℝ)^4513 := by
      have hnat : (10005373913534187747 : ℕ)^1024*10000000000000000^4513 ≤ 10001219166445277^4513*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005373913534187747 10000000000000000000 10001219166445277 10000000000000000 1024 4513 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001219166445277/10000000000000000 : ℝ)) (X := (10005373913534187747/10000000000000000000 : ℝ)) (by norm_num) 4513 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5733538886712601/100000000000000000000 : ℝ) ≤ ((1989597130524986469/1990000000000000000 : ℝ)+2*(20847606667/19900000000000 : ℝ)*(1363/12500 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (1989597130524986469/1990000000000000000 : ℝ)+2*(20847606667/19900000000000 : ℝ)*(1363/12500 : ℝ)=(2000052035307719/2000000000000000 : ℝ) by norm_num, show 1+2*(5733538886712601/100000000000000000000 : ℝ)=(50005733538886712601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5373913534187747/20000000000000000000 : ℝ)+(5733538886712601/100000000000000000000 : ℝ) ≤ ((1989597130524986469/1990000000000000000 : ℝ)+(20847606667/19900000000000 : ℝ)*((15481/100000 : ℝ)+(1363/12500 : ℝ)))^(4513/1024 : ℝ) := by
    rw [show (1989597130524986469/1990000000000000000 : ℝ)+(20847606667/19900000000000 : ℝ)*((15481/100000 : ℝ)+(1363/12500 : ℝ))=(312523114734123/312500000000000 : ℝ) by norm_num, show 1+(5373913534187747/20000000000000000000 : ℝ)+(5733538886712601/100000000000000000000 : ℝ)=(12504075388319706417/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5373913534187747/20000000000000000000 : ℝ) ≤ ((1989597130524986469/1990000000000000000 : ℝ)+2*(20847606667/19900000000000 : ℝ)*(15481/100000 : ℝ))^(4513/1024 : ℝ) := by
    rw [show (1989597130524986469/1990000000000000000 : ℝ)+2*(20847606667/19900000000000 : ℝ)*(15481/100000 : ℝ)=(10001219166445277/10000000000000000 : ℝ) by norm_num, show 1+2*(5373913534187747/20000000000000000000 : ℝ)=(10005373913534187747/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1989597130524986469/1990000000000000000 : ℝ)*(X 1 0+X 2 0)+(20847606667/19900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (1363/12500 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (1989597130524986469/1990000000000000000 : ℝ)) (alpha := (20847606667/19900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1989597130524986469/1990000000000000000 : ℝ)*(X 0 1+X 2 1)+(20847606667/19900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (1363/12500 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (1989597130524986469/1990000000000000000 : ℝ)) (alpha := (20847606667/19900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1989597130524986469/1990000000000000000 : ℝ)*(X 0 2+X 1 2)+(20847606667/19900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4513/1024 : ℝ)) (lo := (1363/12500 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (1989597130524986469/1990000000000000000 : ℝ)) (alpha := (20847606667/19900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414574039/2500000000 : ℝ)*X 0 0+(1350789117/2500000000 : ℝ)*X 0 1+(5403156091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635368563/5000000000 : ℝ)*X 1 0+(-92098027/500000000 : ℝ)*X 1 1+(5403156259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635368389/5000000000 : ℝ)*X 2 0+(5403156523/10000000000 : ℝ)*X 2 1+(-36839213/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((559296347/1250000000 : ℝ)*X 0 0+(4176573409/10000000000 : ℝ)*X 0 1+(1044143231/2500000000 : ℝ)*X 0 2+(559296347/1250000000 : ℝ)*X 1 0+(4176573409/10000000000 : ℝ)*X 1 1+(1044143231/2500000000 : ℝ)*X 1 2+(559296347/1250000000 : ℝ)*X 2 0+(4176573409/10000000000 : ℝ)*X 2 1+(1044143231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1046033099/5000000000 : ℝ)*X 0 0+(1310881643/2500000000 : ℝ)*X 0 1+(5243526641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345475143/2500000000 : ℝ)*X 1 0+(-1907758557/10000000000 : ℝ)*X 1 1+(2621763293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381900511/10000000000 : ℝ)*X 2 0+(2621763343/5000000000 : ℝ)*X 2 1+(-1907758507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4065567529/10000000000 : ℝ)*X 0 0+(4380840103/10000000000 : ℝ)*X 0 1+(438084011/1000000000 : ℝ)*X 0 2+(4065567529/10000000000 : ℝ)*X 1 0+(4380840103/10000000000 : ℝ)*X 1 1+(438084011/1000000000 : ℝ)*X 1 2+(4065567529/10000000000 : ℝ)*X 2 0+(4380840103/10000000000 : ℝ)*X 2 1+(438084011/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-500103973/2500000000 : ℝ)*X 0 0+(5131726773/10000000000 : ℝ)*X 0 1+(2711809111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256481583/10000000000 : ℝ)*X 1 0+(-229159937/1250000000 : ℝ)*X 1 1+(5423618197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314120381/2500000000 : ℝ)*X 2 0+(5423618403/10000000000 : ℝ)*X 2 1+(-1833279293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4525621139/10000000000 : ℝ)*X 0 0+(2075178559/5000000000 : ℝ)*X 0 1+(415035697/1000000000 : ℝ)*X 0 2+(4525621139/10000000000 : ℝ)*X 1 0+(2075178559/5000000000 : ℝ)*X 1 1+(415035697/1000000000 : ℝ)*X 1 2+(4525621139/10000000000 : ℝ)*X 2 0+(2075178559/5000000000 : ℝ)*X 2 1+(415035697/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1749912591/10000000000 : ℝ)*X 0 0+(5511352093/10000000000 : ℝ)*X 0 1+(5228502469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2696181079/5000000000 : ℝ)*X 1 0+(-1913772529/10000000000 : ℝ)*X 1 1+(163390713/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392362287/10000000000 : ℝ)*X 2 0+(5228502737/10000000000 : ℝ)*X 2 1+(-1913772461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2013115231/5000000000 : ℝ)*X 0 0+(4400043487/10000000000 : ℝ)*X 0 1+(220002099/500000000 : ℝ)*X 0 2+(2013115231/5000000000 : ℝ)*X 1 0+(4400043487/10000000000 : ℝ)*X 1 1+(220002099/500000000 : ℝ)*X 1 2+(2013115231/5000000000 : ℝ)*X 2 0+(4400043487/10000000000 : ℝ)*X 2 1+(220002099/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1509_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12747/20000 : ℝ) ≤ (-31707114306312588617050313462241/49750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1340321/25000000000000 : ℝ)*(lower0) + (1141103/10000000000000 : ℝ)*(lower3) + (92357/10000000000000 : ℝ)*(lower4) + (2218979040692863/100000000000000 : ℝ)*(major0) + (2218979040692863/100000000000000 : ℝ)*(major1) + (2218979040692863/100000000000000 : ℝ)*(major2) + (320375533/100000000000000 : ℝ)*(sp1) + (1549515136628063/50000000000000 : ℝ)*(sp4) + (774757574663217/25000000000000 : ℝ)*(sp5) + (1549508418183387/50000000000000 : ℝ)*(sp6) + (1360167199932581/100000000000000 : ℝ)*(sp7) + (86443069/25000000000000 : ℝ)*(sp12) + (3445665407/25000000000000 : ℝ)*(sp14) + (4560117407/100000000000000 : ℝ)*(sp15) + (340042940012497/25000000000000 : ℝ)*(f.failure) + (1549515309514201/50000000000000 : ℝ)*(f.sum) + (382765988723/124375000000000000000000000 : ℝ)*base66 + (984189324613970747/199000000000000000000000000000000 : ℝ)*base67 + (483297531201970747/199000000000000000000000000000000 : ℝ)*base69 + (1035040740858970747/199000000000000000000000000000000 : ℝ)*base71 + (2494238064599/995000000000000000000000000 : ℝ)*base74 + (1592253391686970747/199000000000000000000000000000000 : ℝ)*base75 + (135666987754970747/199000000000000000000000000000000 : ℝ)*base77 + (54362434326029253/199000000000000000000000000000000 : ℝ)*base80 + (2047664242159/995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (958443/125000000000000000000 : ℝ)*base90 + (958443/125000000000000000000 : ℝ)*base92 + (958443/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29307/50000 : ℝ) ≤ (58322974800646854530676717024771/99500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5640989/25000000000000 : ℝ)*(upper2) + (122706477/100000000000000 : ℝ)*(upper3) + (8241343/25000000000000 : ℝ)*(lower5) + (2295019934025551/100000000000000 : ℝ)*(major0) + (2295019934025551/100000000000000 : ℝ)*(major1) + (2295019934025551/100000000000000 : ℝ)*(major2) + (1581859148308889/50000000000000 : ℝ)*(sp0) + (316368430374327/10000000000000 : ℝ)*(sp1) + (395464375451259/12500000000000 : ℝ)*(sp2) + (1406766944802413/100000000000000 : ℝ)*(sp3) + (174491203/5000000000000 : ℝ)*(sp6) + (98408177/50000000000000 : ℝ)*(sp8) + (17094845431/50000000000000 : ℝ)*(sp9) + (15744789209/100000000000000 : ℝ)*(sp11) + (703391344795811/50000000000000 : ℝ)*(f.failure) + (790929623358533/25000000000000 : ℝ)*(f.sum) + (617302598117/248750000000000000000000000 : ℝ)*base66 + (1907266143848030581/199000000000000000000000000000000 : ℝ)*base68 + (2589673243045030581/199000000000000000000000000000000 : ℝ)*base70 + (760667701068030581/199000000000000000000000000000000 : ℝ)*base72 + (766212264337/248750000000000000000000000 : ℝ)*base74 + (507308260287030581/199000000000000000000000000000000 : ℝ)*base76 + (1267657236958030581/199000000000000000000000000000000 : ℝ)*base78 + (756972726778030581/199000000000000000000000000000000 : ℝ)*base80 + (5144212887873/995000000000000000000000000 : ℝ)*base82 + (1706591/250000000000000000000 : ℝ)*base89 + (1706591/250000000000000000000 : ℝ)*base91 + (1706591/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80287/100000 : ℝ) ≤ (9986004849011112945438019635801/12437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7887339/20000000000000 : ℝ)*(lower2) + (952249/20000000000000 : ℝ)*(lower3) + (9648487/100000000000000 : ℝ)*(upper4) + (311159512118019/12500000000000 : ℝ)*(major0) + (311159512118019/12500000000000 : ℝ)*(major1) + (311159512118019/12500000000000 : ℝ)*(major2) + (506799823/20000000000000 : ℝ)*(sp1) + (10229286489/20000000000000 : ℝ)*(sp2) + (371191299/5000000000000 : ℝ)*(sp3) + (499114981/100000000000000 : ℝ)*(sp4) + (3425932277214099/100000000000000 : ℝ)*(sp8) + (856482560582491/25000000000000 : ℝ)*(sp9) + (685176325979327/20000000000000 : ℝ)*(sp10) + (95365551978677/6250000000000 : ℝ)*(sp11) + (381464063871203/25000000000000 : ℝ)*(f.failure) + (85648319408227/2500000000000 : ℝ)*(f.sum) + (1387575731147/497500000000000000000000000 : ℝ)*base65 + (131794888355259911/24875000000000000000000000000000 : ℝ)*base67 + (297525428968259911/24875000000000000000000000000000 : ℝ)*base69 + (332306617352134911/24875000000000000000000000000000 : ℝ)*base71 + (199202620741/62187500000000000000000000 : ℝ)*base74 + (336976062230009911/24875000000000000000000000000000 : ℝ)*base75 + (237668748333134911/24875000000000000000000000000000 : ℝ)*base77 + (59502790702884911/24875000000000000000000000000000 : ℝ)*base79 + (4173504887659/995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (681857/125000000000000000000 : ℝ)*base90 + (681857/125000000000000000000 : ℝ)*base92 + (681857/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85983/100000 : ℝ) ≤ (-85550139684955886037441460616841/99500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18183211/100000000000000 : ℝ)*(upper1) + (160559143/100000000000000 : ℝ)*(lower2) + (337808673/100000000000000 : ℝ)*(upper3) + (16083443/20000000000000 : ℝ)*(upper5) + (2528275447330221/100000000000000 : ℝ)*(major0) + (2528275447330221/100000000000000 : ℝ)*(major1) + (2528275447330221/100000000000000 : ℝ)*(major2) + (131089184833/100000000000000 : ℝ)*(sp5) + (1325553459/6250000000000 : ℝ)*(sp6) + (49981351377/50000000000000 : ℝ)*(sp7) + (1767724573621809/50000000000000 : ℝ)*(sp12) + (1767659029029393/50000000000000 : ℝ)*(sp13) + (141417117535531/4000000000000 : ℝ)*(sp14) + (30993235960177/2000000000000 : ℝ)*(sp15) + (387440440177901/25000000000000 : ℝ)*(f.failure) + (1767724573621809/50000000000000 : ℝ)*(f.sum) + (3950772202047/995000000000000000000000000 : ℝ)*base65 + (2426250515426479649/199000000000000000000000000000000 : ℝ)*base67 + (2674108458922479649/199000000000000000000000000000000 : ℝ)*base69 + (275794398770479649/199000000000000000000000000000000 : ℝ)*base71 + (306776760699/124375000000000000000000000 : ℝ)*base73 + (2327745243194479649/199000000000000000000000000000000 : ℝ)*base75 + (878879610815479649/199000000000000000000000000000000 : ℝ)*base77 + (488244004611479649/199000000000000000000000000000000 : ℝ)*base79 + (867069728149/124375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1173119/125000000000000000000 : ℝ)*base90 + (1173119/125000000000000000000 : ℝ)*base92 + (1173119/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1509_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1363/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12747/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29307/50000 : ℝ) else (80287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85983/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1509_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1509_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12747/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29307/50000 : ℝ) else (80287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85983/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1509_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1509_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4513/1024 : ℝ) ≤ p) (hpb : p ≤ (4515/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8156981/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12747/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29307/50000 : ℝ) else (80287/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85983/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1509_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
