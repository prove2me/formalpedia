-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:46:02.702052+00:00
-- url     : https://prove2.me/submissions/39967430-a83e-4714-aec8-8f1836259411

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
theorem support_rectangle_w1039_s6_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-554269111/2500000000 : ℝ)*x 0 + (5395473799/10000000000 : ℝ)*x 1 + (5263333909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554269111/2500000000 : ℝ)^1029 ≤ (841391533709/6250000000000 : ℝ)^773 := by
    have hnat : (554269111 : ℕ)^1029*6250000000000^773 ≤ 841391533709^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554269111 2500000000 841391533709 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395473799/10000000000 : ℝ)^1029 ≤ (8796580559553/20000000000000 : ℝ)^773 := by
    have hnat : (5395473799 : ℕ)^1029*20000000000000^773 ≤ 8796580559553^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395473799 10000000000 8796580559553 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263333909/10000000000 : ℝ)^1029 ≤ (42554832641067/100000000000000 : ℝ)^773 := by
    have hnat : (5263333909 : ℕ)^1029*100000000000000^773 ≤ 42554832641067^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263333909 10000000000 42554832641067 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554269111/2500000000 : ℝ), (5395473799/10000000000 : ℝ), (5263333909/10000000000 : ℝ)] ![(841391533709/6250000000000 : ℝ), (8796580559553/20000000000000 : ℝ), (42554832641067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554269111/2500000000 : ℝ)|^1029 ≤ (841391533709/6250000000000 : ℝ)^773
        have hw : |(-554269111/2500000000 : ℝ)|=(554269111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395473799/10000000000 : ℝ)|^1029 ≤ (8796580559553/20000000000000 : ℝ)^773
        have hw : |(5395473799/10000000000 : ℝ)|=(5395473799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263333909/10000000000 : ℝ)|^1029 ≤ (42554832641067/100000000000000 : ℝ)^773
        have hw : |(5263333909/10000000000 : ℝ)|=(5263333909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069039131/2000000000 : ℝ)*x 0 + (-2284137529/10000000000 : ℝ)*x 1 + (1315833421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069039131/2000000000 : ℝ)^1029 ≤ (21719076320787/50000000000000 : ℝ)^773 := by
    have hnat : (1069039131 : ℕ)^1029*50000000000000^773 ≤ 21719076320787^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069039131 2000000000 21719076320787 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284137529/10000000000 : ℝ)^1029 ≤ (3501754279003/25000000000000 : ℝ)^773 := by
    have hnat : (2284137529 : ℕ)^1029*25000000000000^773 ≤ 3501754279003^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284137529 10000000000 3501754279003 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315833421/2500000000 : ℝ)^1029 ≤ (8510966043889/20000000000000 : ℝ)^773 := by
    have hnat : (1315833421 : ℕ)^1029*20000000000000^773 ≤ 8510966043889^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315833421 2500000000 8510966043889 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069039131/2000000000 : ℝ), (-2284137529/10000000000 : ℝ), (1315833421/2500000000 : ℝ)] ![(21719076320787/50000000000000 : ℝ), (3501754279003/25000000000000 : ℝ), (8510966043889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069039131/2000000000 : ℝ)|^1029 ≤ (21719076320787/50000000000000 : ℝ)^773
        have hw : |(1069039131/2000000000 : ℝ)|=(1069039131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284137529/10000000000 : ℝ)|^1029 ≤ (3501754279003/25000000000000 : ℝ)^773
        have hw : |(-2284137529/10000000000 : ℝ)|=(2284137529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315833421/2500000000 : ℝ)|^1029 ≤ (8510966043889/20000000000000 : ℝ)^773
        have hw : |(1315833421/2500000000 : ℝ)|=(1315833421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336298821/2500000000 : ℝ)*x 0 + (5263334061/10000000000 : ℝ)*x 1 + (-2284137523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336298821/2500000000 : ℝ)^1029 ≤ (43438148628127/100000000000000 : ℝ)^773 := by
    have hnat : (1336298821 : ℕ)^1029*100000000000000^773 ≤ 43438148628127^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336298821 2500000000 43438148628127 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263334061/10000000000 : ℝ)^1029 ≤ (42554834277007/100000000000000 : ℝ)^773 := by
    have hnat : (5263334061 : ℕ)^1029*100000000000000^773 ≤ 42554834277007^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263334061 10000000000 42554834277007 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284137523/10000000000 : ℝ)^1029 ≤ (14007017067033/100000000000000 : ℝ)^773 := by
    have hnat : (2284137523 : ℕ)^1029*100000000000000^773 ≤ 14007017067033^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284137523 10000000000 14007017067033 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336298821/2500000000 : ℝ), (5263334061/10000000000 : ℝ), (-2284137523/10000000000 : ℝ)] ![(43438148628127/100000000000000 : ℝ), (42554834277007/100000000000000 : ℝ), (14007017067033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336298821/2500000000 : ℝ)|^1029 ≤ (43438148628127/100000000000000 : ℝ)^773
        have hw : |(1336298821/2500000000 : ℝ)|=(1336298821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263334061/10000000000 : ℝ)|^1029 ≤ (42554834277007/100000000000000 : ℝ)^773
        have hw : |(5263334061/10000000000 : ℝ)|=(5263334061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284137523/10000000000 : ℝ)|^1029 ≤ (14007017067033/100000000000000 : ℝ)^773
        have hw : |(-2284137523/10000000000 : ℝ)|=(2284137523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (43793563/100000000 : ℝ)*x 0 + (2126247569/5000000000 : ℝ)*x 1 + (1127520619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43793563/100000000 : ℝ)^1029 ≤ (8329012971557/25000000000000 : ℝ)^773 := by
    have hnat : (43793563 : ℕ)^1029*25000000000000^773 ≤ 8329012971557^773*100000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43793563 100000000 8329012971557 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126247569/5000000000 : ℝ)^1029 ≤ (32037536651171/100000000000000 : ℝ)^773 := by
    have hnat : (2126247569 : ℕ)^1029*100000000000000^773 ≤ 32037536651171^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126247569 5000000000 32037536651171 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127520619/2500000000 : ℝ)^1029 ≤ (34646411452199/100000000000000 : ℝ)^773 := by
    have hnat : (1127520619 : ℕ)^1029*100000000000000^773 ≤ 34646411452199^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127520619 2500000000 34646411452199 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43793563/100000000 : ℝ), (2126247569/5000000000 : ℝ), (1127520619/2500000000 : ℝ)] ![(8329012971557/25000000000000 : ℝ), (32037536651171/100000000000000 : ℝ), (34646411452199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43793563/100000000 : ℝ)|^1029 ≤ (8329012971557/25000000000000 : ℝ)^773
        have hw : |(43793563/100000000 : ℝ)|=(43793563/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126247569/5000000000 : ℝ)|^1029 ≤ (32037536651171/100000000000000 : ℝ)^773
        have hw : |(2126247569/5000000000 : ℝ)|=(2126247569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127520619/2500000000 : ℝ)|^1029 ≤ (34646411452199/100000000000000 : ℝ)^773
        have hw : |(1127520619/2500000000 : ℝ)|=(1127520619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-443416517/2000000000 : ℝ)*x 0 + (263183381/500000000 : ℝ)*x 1 + (5395138237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443416517/2000000000 : ℝ)^1029 ≤ (3365578544289/25000000000000 : ℝ)^773 := by
    have hnat : (443416517 : ℕ)^1029*25000000000000^773 ≤ 3365578544289^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443416517 2000000000 3365578544289 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263183381/500000000 : ℝ)^1029 ≤ (42558424331739/100000000000000 : ℝ)^773 := by
    have hnat : (263183381 : ℕ)^1029*100000000000000^773 ≤ 42558424331739^773*500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263183381 500000000 42558424331739 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395138237/10000000000 : ℝ)^1029 ≤ (43979261480811/100000000000000 : ℝ)^773 := by
    have hnat : (5395138237 : ℕ)^1029*100000000000000^773 ≤ 43979261480811^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395138237 10000000000 43979261480811 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443416517/2000000000 : ℝ), (263183381/500000000 : ℝ), (5395138237/10000000000 : ℝ)] ![(3365578544289/25000000000000 : ℝ), (42558424331739/100000000000000 : ℝ), (43979261480811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443416517/2000000000 : ℝ)|^1029 ≤ (3365578544289/25000000000000 : ℝ)^773
        have hw : |(-443416517/2000000000 : ℝ)|=(443416517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263183381/500000000 : ℝ)|^1029 ≤ (42558424331739/100000000000000 : ℝ)^773
        have hw : |(263183381/500000000 : ℝ)|=(263183381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395138237/10000000000 : ℝ)|^1029 ≤ (43979261480811/100000000000000 : ℝ)^773
        have hw : |(5395138237/10000000000 : ℝ)|=(5395138237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311984511/10000000000 : ℝ)*x 0 + (-538083277/2500000000 : ℝ)*x 1 + (1079027659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311984511/10000000000 : ℝ)^1029 ≤ (336556620427/781250000000 : ℝ)^773 := by
    have hnat : (5311984511 : ℕ)^1029*781250000000^773 ≤ 336556620427^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311984511 10000000000 336556620427 781250000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538083277/2500000000 : ℝ)^1029 ≤ (3235372616021/25000000000000 : ℝ)^773 := by
    have hnat : (538083277 : ℕ)^1029*25000000000000^773 ≤ 3235372616021^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538083277 2500000000 3235372616021 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079027659/2000000000 : ℝ)^1029 ≤ (21989631055093/50000000000000 : ℝ)^773 := by
    have hnat : (1079027659 : ℕ)^1029*50000000000000^773 ≤ 21989631055093^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079027659 2000000000 21989631055093 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311984511/10000000000 : ℝ), (-538083277/2500000000 : ℝ), (1079027659/2000000000 : ℝ)] ![(336556620427/781250000000 : ℝ), (3235372616021/25000000000000 : ℝ), (21989631055093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311984511/10000000000 : ℝ)|^1029 ≤ (336556620427/781250000000 : ℝ)^773
        have hw : |(5311984511/10000000000 : ℝ)|=(5311984511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538083277/2500000000 : ℝ)|^1029 ≤ (3235372616021/25000000000000 : ℝ)^773
        have hw : |(-538083277/2500000000 : ℝ)|=(538083277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079027659/2000000000 : ℝ)|^1029 ≤ (21989631055093/50000000000000 : ℝ)^773
        have hw : |(1079027659/2000000000 : ℝ)|=(1079027659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311984521/10000000000 : ℝ)*x 0 + (674392281/1250000000 : ℝ)*x 1 + (-1076166579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311984521/10000000000 : ℝ)^1029 ≤ (10769811880653/25000000000000 : ℝ)^773 := by
    have hnat : (5311984521 : ℕ)^1029*25000000000000^773 ≤ 10769811880653^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311984521 10000000000 10769811880653 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674392281/1250000000 : ℝ)^1029 ≤ (2748703850011/6250000000000 : ℝ)^773 := by
    have hnat : (674392281 : ℕ)^1029*6250000000000^773 ≤ 2748703850011^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674392281 1250000000 2748703850011 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076166579/5000000000 : ℝ)^1029 ≤ (404421589509/3125000000000 : ℝ)^773 := by
    have hnat : (1076166579 : ℕ)^1029*3125000000000^773 ≤ 404421589509^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076166579 5000000000 404421589509 3125000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311984521/10000000000 : ℝ), (674392281/1250000000 : ℝ), (-1076166579/5000000000 : ℝ)] ![(10769811880653/25000000000000 : ℝ), (2748703850011/6250000000000 : ℝ), (404421589509/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311984521/10000000000 : ℝ)|^1029 ≤ (10769811880653/25000000000000 : ℝ)^773
        have hw : |(5311984521/10000000000 : ℝ)|=(5311984521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674392281/1250000000 : ℝ)|^1029 ≤ (2748703850011/6250000000000 : ℝ)^773
        have hw : |(674392281/1250000000 : ℝ)|=(674392281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076166579/5000000000 : ℝ)|^1029 ≤ (404421589509/3125000000000 : ℝ)^773
        have hw : |(-1076166579/5000000000 : ℝ)|=(1076166579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s6_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (547420967/1250000000 : ℝ)*x 0 + (5636789/12500000 : ℝ)*x 1 + (2126573821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547420967/1250000000 : ℝ)^1029 ≤ (16658083849101/50000000000000 : ℝ)^773 := by
    have hnat : (547420967 : ℕ)^1029*50000000000000^773 ≤ 16658083849101^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547420967 1250000000 16658083849101 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5636789/12500000 : ℝ)^1029 ≤ (34639751603777/100000000000000 : ℝ)^773 := by
    have hnat : (5636789 : ℕ)^1029*100000000000000^773 ≤ 34639751603777^773*12500000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636789 12500000 34639751603777 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126573821/5000000000 : ℝ)^1029 ≤ (16022040341353/50000000000000 : ℝ)^773 := by
    have hnat : (2126573821 : ℕ)^1029*50000000000000^773 ≤ 16022040341353^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126573821 5000000000 16022040341353 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547420967/1250000000 : ℝ), (5636789/12500000 : ℝ), (2126573821/5000000000 : ℝ)] ![(16658083849101/50000000000000 : ℝ), (34639751603777/100000000000000 : ℝ), (16022040341353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547420967/1250000000 : ℝ)|^1029 ≤ (16658083849101/50000000000000 : ℝ)^773
        have hw : |(547420967/1250000000 : ℝ)|=(547420967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5636789/12500000 : ℝ)|^1029 ≤ (34639751603777/100000000000000 : ℝ)^773
        have hw : |(5636789/12500000 : ℝ)|=(5636789/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126573821/5000000000 : ℝ)|^1029 ≤ (16022040341353/50000000000000 : ℝ)^773
        have hw : |(2126573821/5000000000 : ℝ)|=(2126573821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11201/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7/50 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5577/50000 : ℝ) ^ (8231/2048 : ℝ) ≤ (1855636152461723/12500000000000000000 : ℝ) := by
    have hpowers : (5577/50000 : ℝ)^8231 ≤ (1855636152461723/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5577 : ℕ)^8231*12500000000000000000^2048 ≤ 1855636152461723^2048*50000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5577 50000 1855636152461723 12500000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5577/50000 : ℝ)) (X := (1855636152461723/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (8231/2048 : ℝ) ≤ (3751682208837607/10000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^8231 ≤ (3751682208837607/10000000000000000000 : ℝ)^2048 := by
      have hnat : (439 : ℕ)^8231*10000000000000000000^2048 ≤ 3751682208837607^2048*3125^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 3751682208837607 10000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (3751682208837607/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251855636152461723/6250000000000000000 : ℝ) ≤ (2000147731031357/2000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (6251855636152461723/6250000000000000000 : ℝ)^2048 ≤ (2000147731031357/2000000000000000 : ℝ)^8231 := by
      have hnat : (6251855636152461723 : ℕ)^2048*2000000000000000^8231 ≤ 2000147731031357^8231*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251855636152461723 6250000000000000000 2000147731031357 2000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000147731031357/2000000000000000 : ℝ)) (X := (6251855636152461723/6250000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026180955654034927/50000000000000000000 : ℝ) ≤ (5000651294561743/5000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50026180955654034927/50000000000000000000 : ℝ)^2048 ≤ (5000651294561743/5000000000000000 : ℝ)^8231 := by
      have hnat : (50026180955654034927 : ℕ)^2048*5000000000000000^8231 ≤ 5000651294561743^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026180955654034927 50000000000000000000 5000651294561743 5000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000651294561743/5000000000000000 : ℝ)) (X := (50026180955654034927/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003751682208837607/5000000000000000000 : ℝ) ≤ (10001866523090187/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (5003751682208837607/5000000000000000000 : ℝ)^2048 ≤ (10001866523090187/10000000000000000 : ℝ)^8231 := by
      have hnat : (5003751682208837607 : ℕ)^2048*10000000000000000^8231 ≤ 10001866523090187^8231*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003751682208837607 5000000000000000000 10001866523090187 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001866523090187/10000000000000000 : ℝ)) (X := (5003751682208837607/5000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1855636152461723/12500000000000000000 : ℝ) ≤ ((14464778714547284941/14470000000000000000 : ℝ)+2*(563933966701/289400000000000 : ℝ)*(5577/50000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (14464778714547284941/14470000000000000000 : ℝ)+2*(563933966701/289400000000000 : ℝ)*(5577/50000 : ℝ)=(2000147731031357/2000000000000000 : ℝ) by norm_num, show 1+2*(1855636152461723/12500000000000000000 : ℝ)=(6251855636152461723/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3751682208837607/10000000000000000000 : ℝ)+(1855636152461723/12500000000000000000 : ℝ) ≤ ((14464778714547284941/14470000000000000000 : ℝ)+(563933966701/289400000000000 : ℝ)*((439/3125 : ℝ)+(5577/50000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (14464778714547284941/14470000000000000000 : ℝ)+(563933966701/289400000000000 : ℝ)*((439/3125 : ℝ)+(5577/50000 : ℝ))=(5000651294561743/5000000000000000 : ℝ) by norm_num, show 1+(3751682208837607/10000000000000000000 : ℝ)+(1855636152461723/12500000000000000000 : ℝ)=(50026180955654034927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3751682208837607/10000000000000000000 : ℝ) ≤ ((14464778714547284941/14470000000000000000 : ℝ)+2*(563933966701/289400000000000 : ℝ)*(439/3125 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (14464778714547284941/14470000000000000000 : ℝ)+2*(563933966701/289400000000000 : ℝ)*(439/3125 : ℝ)=(10001866523090187/10000000000000000 : ℝ) by norm_num, show 1+2*(3751682208837607/10000000000000000000 : ℝ)=(5003751682208837607/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14464778714547284941/14470000000000000000 : ℝ)*(X 1 0+X 2 0)+(563933966701/289400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (14464778714547284941/14470000000000000000 : ℝ)) (alpha := (563933966701/289400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14464778714547284941/14470000000000000000 : ℝ)*(X 0 1+X 2 1)+(563933966701/289400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (14464778714547284941/14470000000000000000 : ℝ)) (alpha := (563933966701/289400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14464778714547284941/14470000000000000000 : ℝ)*(X 0 2+X 1 2)+(563933966701/289400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (14464778714547284941/14470000000000000000 : ℝ)) (alpha := (563933966701/289400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-554269111/2500000000 : ℝ)*X 0 0+(5395473799/10000000000 : ℝ)*X 0 1+(5263333909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069039131/2000000000 : ℝ)*X 1 0+(-2284137529/10000000000 : ℝ)*X 1 1+(1315833421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336298821/2500000000 : ℝ)*X 2 0+(5263334061/10000000000 : ℝ)*X 2 1+(-2284137523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43793563/100000000 : ℝ)*X 0 0+(2126247569/5000000000 : ℝ)*X 0 1+(1127520619/2500000000 : ℝ)*X 0 2+(43793563/100000000 : ℝ)*X 1 0+(2126247569/5000000000 : ℝ)*X 1 1+(1127520619/2500000000 : ℝ)*X 1 2+(43793563/100000000 : ℝ)*X 2 0+(2126247569/5000000000 : ℝ)*X 2 1+(1127520619/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-443416517/2000000000 : ℝ)*X 0 0+(263183381/500000000 : ℝ)*X 0 1+(5395138237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311984511/10000000000 : ℝ)*X 1 0+(-538083277/2500000000 : ℝ)*X 1 1+(1079027659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311984521/10000000000 : ℝ)*X 2 0+(674392281/1250000000 : ℝ)*X 2 1+(-1076166579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547420967/1250000000 : ℝ)*X 0 0+(5636789/12500000 : ℝ)*X 0 1+(2126573821/5000000000 : ℝ)*X 0 2+(547420967/1250000000 : ℝ)*X 1 0+(5636789/12500000 : ℝ)*X 1 1+(2126573821/5000000000 : ℝ)*X 1 2+(547420967/1250000000 : ℝ)*X 2 0+(5636789/12500000 : ℝ)*X 2 1+(2126573821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1966419711059352375613813473/723500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57922727/20000000000000 : ℝ)*(base8) + (288732347/50000000000000 : ℝ)*(base21) + (155940351/50000000000000 : ℝ)*(lower3) + (2393153/20000000000000 : ℝ)*(lower4) + (45196363/25000000000000 : ℝ)*(lower5) + (5724975181177449/100000000000000 : ℝ)*(major0) + (5724975181177449/100000000000000 : ℝ)*(major1) + (5724975181177449/100000000000000 : ℝ)*(major2) + (1891937089653053/25000000000000 : ℝ)*(sp0) + (7567770956991177/100000000000000 : ℝ)*(sp1) + (7567770379526483/100000000000000 : ℝ)*(sp2) + (970544688193129/25000000000000 : ℝ)*(sp3) + (2230876533/10000000000000 : ℝ)*(sp4) + (112398731/20000000000000 : ℝ)*(sp7) + (3882179314766171/100000000000000 : ℝ)*(f.failure) + (7567770956991177/100000000000000 : ℝ)*(f.sum) + (47557893057809/14470000000000000000000000000 : ℝ)*base65 + (16223354156161945509/1447000000000000000000000000000000 : ℝ)*base67 + (6447011673894054491/1447000000000000000000000000000000 : ℝ)*base70 + (14484073730468945509/1447000000000000000000000000000000 : ℝ)*base71 + (6216699735499/14470000000000000000000000000 : ℝ)*base73 + (2758443932944054491/1447000000000000000000000000000000 : ℝ)*base76 + (5930899797529945509/1447000000000000000000000000000000 : ℝ)*base77 + (16978124585836945509/1447000000000000000000000000000000 : ℝ)*base79 + (1803123285241/14470000000000000000000000000 : ℝ)*base82 + (42023167/10000000000000000000000 : ℝ)*base89 + (42023167/10000000000000000000000 : ℝ)*base91 + (42023167/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7790032076832027612292333503/723500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2161612491/100000000000000 : ℝ)*(base19) + (584186219/25000000000000 : ℝ)*(base23) + (56833117/25000000000000 : ℝ)*(upper3) + (89209761/100000000000000 : ℝ)*(lower4) + (30254239/10000000000000 : ℝ)*(upper5) + (5754094756909161/100000000000000 : ℝ)*(major0) + (5754094756909161/100000000000000 : ℝ)*(major1) + (5754094756909161/100000000000000 : ℝ)*(major2) + (61619734729/100000000000000 : ℝ)*(sp1) + (30240229237/50000000000000 : ℝ)*(sp2) + (760626348125779/10000000000000 : ℝ)*(sp4) + (760619969991057/10000000000000 : ℝ)*(sp5) + (190155016601361/2500000000000 : ℝ)*(sp6) + (243870354603473/6250000000000 : ℝ)*(sp7) + (243870354603473/6250000000000 : ℝ)*(f.failure) + (760626348125779/10000000000000 : ℝ)*(f.sum) + (123408623166199/14470000000000000000000000000 : ℝ)*base66 + (23868585999886705499/1447000000000000000000000000000000 : ℝ)*base68 + (1095628861871294501/1447000000000000000000000000000000 : ℝ)*base69 + (9199271029497705499/1447000000000000000000000000000000 : ℝ)*base72 + (135532435675669/14470000000000000000000000000 : ℝ)*base74 + (23343439373660705499/1447000000000000000000000000000000 : ℝ)*base76 + (713160233174705499/1447000000000000000000000000000000 : ℝ)*base78 + (15196443093515294501/1447000000000000000000000000000000 : ℝ)*base79 + (12744412168119/14470000000000000000000000000 : ℝ)*base82 + (4581421/625000000000000000000 : ℝ)*base89 + (4581421/625000000000000000000 : ℝ)*base91 + (4581421/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1039_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7/50 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_s7_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1108559669/5000000000 : ℝ)*x 0 + (2697473719/5000000000 : ℝ)*x 1 + (5263832381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1108559669/5000000000 : ℝ)^1029 ≤ (13462611253259/100000000000000 : ℝ)^773 := by
    have hnat : (1108559669 : ℕ)^1029*100000000000000^773 ≤ 13462611253259^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108559669 5000000000 13462611253259 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697473719/5000000000 : ℝ)^1029 ≤ (21988595539147/50000000000000 : ℝ)^773 := by
    have hnat : (2697473719 : ℕ)^1029*50000000000000^773 ≤ 21988595539147^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697473719 5000000000 21988595539147 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263832381/10000000000 : ℝ)^1029 ≤ (42560197662037/100000000000000 : ℝ)^773 := by
    have hnat : (5263832381 : ℕ)^1029*100000000000000^773 ≤ 42560197662037^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263832381 10000000000 42560197662037 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1108559669/5000000000 : ℝ), (2697473719/5000000000 : ℝ), (5263832381/10000000000 : ℝ)] ![(13462611253259/100000000000000 : ℝ), (21988595539147/50000000000000 : ℝ), (42560197662037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1108559669/5000000000 : ℝ)|^1029 ≤ (13462611253259/100000000000000 : ℝ)^773
        have hw : |(-1108559669/5000000000 : ℝ)|=(1108559669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697473719/5000000000 : ℝ)|^1029 ≤ (21988595539147/50000000000000 : ℝ)^773
        have hw : |(2697473719/5000000000 : ℝ)|=(2697473719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263832381/10000000000 : ℝ)|^1029 ≤ (42560197662037/100000000000000 : ℝ)^773
        have hw : |(5263832381/10000000000 : ℝ)|=(5263832381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672532863/5000000000 : ℝ)*x 0 + (-2283652423/10000000000 : ℝ)*x 1 + (2631916097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672532863/5000000000 : ℝ)^1029 ≤ (43436747086171/100000000000000 : ℝ)^773 := by
    have hnat : (2672532863 : ℕ)^1029*100000000000000^773 ≤ 43436747086171^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672532863 5000000000 43436747086171 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283652423/10000000000 : ℝ)^1029 ≤ (2800611449687/20000000000000 : ℝ)^773 := by
    have hnat : (2283652423 : ℕ)^1029*20000000000000^773 ≤ 2800611449687^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283652423 10000000000 2800611449687 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631916097/5000000000 : ℝ)^1029 ≤ (5320024456167/12500000000000 : ℝ)^773 := by
    have hnat : (2631916097 : ℕ)^1029*12500000000000^773 ≤ 5320024456167^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631916097 5000000000 5320024456167 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672532863/5000000000 : ℝ), (-2283652423/10000000000 : ℝ), (2631916097/5000000000 : ℝ)] ![(43436747086171/100000000000000 : ℝ), (2800611449687/20000000000000 : ℝ), (5320024456167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672532863/5000000000 : ℝ)|^1029 ≤ (43436747086171/100000000000000 : ℝ)^773
        have hw : |(2672532863/5000000000 : ℝ)|=(2672532863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2283652423/10000000000 : ℝ)|^1029 ≤ (2800611449687/20000000000000 : ℝ)^773
        have hw : |(-2283652423/10000000000 : ℝ)|=(2283652423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631916097/5000000000 : ℝ)|^1029 ≤ (5320024456167/12500000000000 : ℝ)^773
        have hw : |(2631916097/5000000000 : ℝ)|=(2631916097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672532833/5000000000 : ℝ)*x 0 + (5263832337/10000000000 : ℝ)*x 1 + (-1141826157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672532833/5000000000 : ℝ)^1029 ≤ (43436746437101/100000000000000 : ℝ)^773 := by
    have hnat : (2672532833 : ℕ)^1029*100000000000000^773 ≤ 43436746437101^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672532833 5000000000 43436746437101 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263832337/10000000000 : ℝ)^1029 ≤ (2128009859423/5000000000000 : ℝ)^773 := by
    have hnat : (5263832337 : ℕ)^1029*5000000000000^773 ≤ 2128009859423^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263832337 10000000000 2128009859423 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141826157/5000000000 : ℝ)^1029 ≤ (14003056358711/100000000000000 : ℝ)^773 := by
    have hnat : (1141826157 : ℕ)^1029*100000000000000^773 ≤ 14003056358711^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141826157 5000000000 14003056358711 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672532833/5000000000 : ℝ), (5263832337/10000000000 : ℝ), (-1141826157/5000000000 : ℝ)] ![(43436746437101/100000000000000 : ℝ), (2128009859423/5000000000000 : ℝ), (14003056358711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672532833/5000000000 : ℝ)|^1029 ≤ (43436746437101/100000000000000 : ℝ)^773
        have hw : |(2672532833/5000000000 : ℝ)|=(2672532833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263832337/10000000000 : ℝ)|^1029 ≤ (2128009859423/5000000000000 : ℝ)^773
        have hw : |(5263832337/10000000000 : ℝ)|=(5263832337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1141826157/5000000000 : ℝ)|^1029 ≤ (14003056358711/100000000000000 : ℝ)^773
        have hw : |(-1141826157/5000000000 : ℝ)|=(1141826157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4379383637/10000000000 : ℝ)*x 0 + (4253489267/10000000000 : ℝ)*x 1 + (36072643/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379383637/10000000000 : ℝ)^1029 ≤ (16658164363621/50000000000000 : ℝ)^773 := by
    have hnat : (4379383637 : ℕ)^1029*50000000000000^773 ≤ 16658164363621^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379383637 10000000000 16658164363621 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253489267/10000000000 : ℝ)^1029 ≤ (32047507008529/100000000000000 : ℝ)^773 := by
    have hnat : (4253489267 : ℕ)^1029*100000000000000^773 ≤ 32047507008529^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253489267 10000000000 32047507008529 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36072643/80000000 : ℝ)^1029 ≤ (1385446570127/4000000000000 : ℝ)^773 := by
    have hnat : (36072643 : ℕ)^1029*4000000000000^773 ≤ 1385446570127^773*80000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36072643 80000000 1385446570127 4000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379383637/10000000000 : ℝ), (4253489267/10000000000 : ℝ), (36072643/80000000 : ℝ)] ![(16658164363621/50000000000000 : ℝ), (32047507008529/100000000000000 : ℝ), (1385446570127/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379383637/10000000000 : ℝ)|^1029 ≤ (16658164363621/50000000000000 : ℝ)^773
        have hw : |(4379383637/10000000000 : ℝ)|=(4379383637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253489267/10000000000 : ℝ)|^1029 ≤ (32047507008529/100000000000000 : ℝ)^773
        have hw : |(4253489267/10000000000 : ℝ)|=(4253489267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36072643/80000000 : ℝ)|^1029 ≤ (1385446570127/4000000000000 : ℝ)^773
        have hw : |(36072643/80000000 : ℝ)|=(36072643/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-110856227/500000000 : ℝ)*x 0 + (658020119/1250000000 : ℝ)*x 1 + (5394617651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110856227/500000000 : ℝ)^1029 ≤ (1682831662673/12500000000000 : ℝ)^773 := by
    have hnat : (110856227 : ℕ)^1029*12500000000000^773 ≤ 1682831662673^773*500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110856227 500000000 1682831662673 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658020119/1250000000 : ℝ)^1029 ≤ (1330116691933/3125000000000 : ℝ)^773 := by
    have hnat : (658020119 : ℕ)^1029*3125000000000^773 ≤ 1330116691933^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658020119 1250000000 1330116691933 3125000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394617651/10000000000 : ℝ)^1029 ≤ (43973612543159/100000000000000 : ℝ)^773 := by
    have hnat : (5394617651 : ℕ)^1029*100000000000000^773 ≤ 43973612543159^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394617651 10000000000 43973612543159 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110856227/500000000 : ℝ), (658020119/1250000000 : ℝ), (5394617651/10000000000 : ℝ)] ![(1682831662673/12500000000000 : ℝ), (1330116691933/3125000000000 : ℝ), (43973612543159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110856227/500000000 : ℝ)|^1029 ≤ (1682831662673/12500000000000 : ℝ)^773
        have hw : |(-110856227/500000000 : ℝ)|=(110856227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658020119/1250000000 : ℝ)|^1029 ≤ (1330116691933/3125000000000 : ℝ)^773
        have hw : |(658020119/1250000000 : ℝ)|=(658020119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394617651/10000000000 : ℝ)|^1029 ≤ (43973612543159/100000000000000 : ℝ)^773
        have hw : |(5394617651/10000000000 : ℝ)|=(5394617651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312111967/10000000000 : ℝ)*x 0 + (-1076433519/5000000000 : ℝ)*x 1 + (2697308817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312111967/10000000000 : ℝ)^1029 ≤ (10770155846349/25000000000000 : ℝ)^773 := by
    have hnat : (5312111967 : ℕ)^1029*25000000000000^773 ≤ 10770155846349^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312111967 10000000000 10770155846349 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076433519/5000000000 : ℝ)^1029 ≤ (12945764250881/100000000000000 : ℝ)^773 := by
    have hnat : (1076433519 : ℕ)^1029*100000000000000^773 ≤ 12945764250881^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076433519 5000000000 12945764250881 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697308817/5000000000 : ℝ)^1029 ≤ (43973612358693/100000000000000 : ℝ)^773 := by
    have hnat : (2697308817 : ℕ)^1029*100000000000000^773 ≤ 43973612358693^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697308817 5000000000 43973612358693 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312111967/10000000000 : ℝ), (-1076433519/5000000000 : ℝ), (2697308817/5000000000 : ℝ)] ![(10770155846349/25000000000000 : ℝ), (12945764250881/100000000000000 : ℝ), (43973612358693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312111967/10000000000 : ℝ)|^1029 ≤ (10770155846349/25000000000000 : ℝ)^773
        have hw : |(5312111967/10000000000 : ℝ)|=(5312111967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076433519/5000000000 : ℝ)|^1029 ≤ (12945764250881/100000000000000 : ℝ)^773
        have hw : |(-1076433519/5000000000 : ℝ)|=(1076433519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697308817/5000000000 : ℝ)|^1029 ≤ (43973612358693/100000000000000 : ℝ)^773
        have hw : |(2697308817/5000000000 : ℝ)|=(2697308817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312112007/10000000000 : ℝ)*x 0 + (5394617609/10000000000 : ℝ)*x 1 + (-2152867017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312112007/10000000000 : ℝ)^1029 ≤ (5385077977153/12500000000000 : ℝ)^773 := by
    have hnat : (5312112007 : ℕ)^1029*12500000000000^773 ≤ 5385077977153^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312112007 10000000000 5385077977153 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394617609/10000000000 : ℝ)^1029 ≤ (2198680604371/5000000000000 : ℝ)^773 := by
    have hnat : (5394617609 : ℕ)^1029*5000000000000^773 ≤ 2198680604371^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394617609 10000000000 2198680604371 5000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152867017/10000000000 : ℝ)^1029 ≤ (6472882041391/50000000000000 : ℝ)^773 := by
    have hnat : (2152867017 : ℕ)^1029*50000000000000^773 ≤ 6472882041391^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152867017 10000000000 6472882041391 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312112007/10000000000 : ℝ), (5394617609/10000000000 : ℝ), (-2152867017/10000000000 : ℝ)] ![(5385077977153/12500000000000 : ℝ), (2198680604371/5000000000000 : ℝ), (6472882041391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312112007/10000000000 : ℝ)|^1029 ≤ (5385077977153/12500000000000 : ℝ)^773
        have hw : |(5312112007/10000000000 : ℝ)|=(5312112007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394617609/10000000000 : ℝ)|^1029 ≤ (2198680604371/5000000000000 : ℝ)^773
        have hw : |(5394617609/10000000000 : ℝ)|=(5394617609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152867017/10000000000 : ℝ)|^1029 ≤ (6472882041391/50000000000000 : ℝ)^773
        have hw : |(-2152867017/10000000000 : ℝ)|=(2152867017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s7_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4379393559/10000000000 : ℝ)*x 0 + (4508439689/10000000000 : ℝ)*x 1 + (850826481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379393559/10000000000 : ℝ)^1029 ≤ (33316429207193/100000000000000 : ℝ)^773 := by
    have hnat : (4379393559 : ℕ)^1029*100000000000000^773 ≤ 33316429207193^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379393559 10000000000 33316429207193 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508439689/10000000000 : ℝ)^1029 ≤ (8657403294021/25000000000000 : ℝ)^773 := by
    have hnat : (4508439689 : ℕ)^1029*25000000000000^773 ≤ 8657403294021^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508439689 10000000000 8657403294021 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850826481/2000000000 : ℝ)^1029 ≤ (6410791520881/20000000000000 : ℝ)^773 := by
    have hnat : (850826481 : ℕ)^1029*20000000000000^773 ≤ 6410791520881^773*2000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850826481 2000000000 6410791520881 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379393559/10000000000 : ℝ), (4508439689/10000000000 : ℝ), (850826481/2000000000 : ℝ)] ![(33316429207193/100000000000000 : ℝ), (8657403294021/25000000000000 : ℝ), (6410791520881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379393559/10000000000 : ℝ)|^1029 ≤ (33316429207193/100000000000000 : ℝ)^773
        have hw : |(4379393559/10000000000 : ℝ)|=(4379393559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508439689/10000000000 : ℝ)|^1029 ≤ (8657403294021/25000000000000 : ℝ)^773
        have hw : |(4508439689/10000000000 : ℝ)|=(4508439689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850826481/2000000000 : ℝ)|^1029 ≤ (6410791520881/20000000000000 : ℝ)^773
        have hw : |(850826481/2000000000 : ℝ)|=(850826481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3497/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7/50 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7/50 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7/50 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11201/100000 : ℝ) ^ (8231/2048 : ℝ) ≤ (7549048579863731/50000000000000000000 : ℝ) := by
    have hpowers : (11201/100000 : ℝ)^8231 ≤ (7549048579863731/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11201 : ℕ)^8231*50000000000000000000^2048 ≤ 7549048579863731^2048*100000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11201 100000 7549048579863731 50000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11201/100000 : ℝ)) (X := (7549048579863731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7/50 : ℝ) ^ (8231/2048 : ℝ) ≤ (37004273789425349/100000000000000000000 : ℝ) := by
    have hpowers : (7/50 : ℝ)^8231 ≤ (37004273789425349/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7 : ℕ)^8231*100000000000000000000^2048 ≤ 37004273789425349^2048*50^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7 50 37004273789425349 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7/50 : ℝ)) (X := (37004273789425349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007549048579863731/25000000000000000000 : ℝ) ≤ (2000150248556531/2000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (25007549048579863731/25000000000000000000 : ℝ)^2048 ≤ (2000150248556531/2000000000000000 : ℝ)^8231 := by
      have hnat : (25007549048579863731 : ℕ)^2048*2000000000000000^8231 ≤ 2000150248556531^8231*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007549048579863731 25000000000000000000 2000150248556531 2000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000150248556531/2000000000000000 : ℝ)) (X := (25007549048579863731/25000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052102370949152811/100000000000000000000 : ℝ) ≤ (10001296133890877/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (100052102370949152811/100000000000000000000 : ℝ)^2048 ≤ (10001296133890877/10000000000000000 : ℝ)^8231 := by
      have hnat : (100052102370949152811 : ℕ)^2048*10000000000000000^8231 ≤ 10001296133890877^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052102370949152811 100000000000000000000 10001296133890877 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001296133890877/10000000000000000 : ℝ)) (X := (100052102370949152811/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037004273789425349/50000000000000000000 : ℝ) ≤ (10001841024999099/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50037004273789425349/50000000000000000000 : ℝ)^2048 ≤ (10001841024999099/10000000000000000 : ℝ)^8231 := by
      have hnat : (50037004273789425349 : ℕ)^2048*10000000000000000^8231 ≤ 10001841024999099^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037004273789425349 50000000000000000000 10001841024999099 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001841024999099/10000000000000000 : ℝ)) (X := (50037004273789425349/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7549048579863731/50000000000000000000 : ℝ) ≤ ((27979896077942262101/27990000000000000000 : ℝ)+2*(272445554111/139950000000000 : ℝ)*(11201/100000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (27979896077942262101/27990000000000000000 : ℝ)+2*(272445554111/139950000000000 : ℝ)*(11201/100000 : ℝ)=(2000150248556531/2000000000000000 : ℝ) by norm_num, show 1+2*(7549048579863731/50000000000000000000 : ℝ)=(25007549048579863731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37004273789425349/100000000000000000000 : ℝ)+(7549048579863731/50000000000000000000 : ℝ) ≤ ((27979896077942262101/27990000000000000000 : ℝ)+(272445554111/139950000000000 : ℝ)*((7/50 : ℝ)+(11201/100000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (27979896077942262101/27990000000000000000 : ℝ)+(272445554111/139950000000000 : ℝ)*((7/50 : ℝ)+(11201/100000 : ℝ))=(10001296133890877/10000000000000000 : ℝ) by norm_num, show 1+(37004273789425349/100000000000000000000 : ℝ)+(7549048579863731/50000000000000000000 : ℝ)=(100052102370949152811/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37004273789425349/100000000000000000000 : ℝ) ≤ ((27979896077942262101/27990000000000000000 : ℝ)+2*(272445554111/139950000000000 : ℝ)*(7/50 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (27979896077942262101/27990000000000000000 : ℝ)+2*(272445554111/139950000000000 : ℝ)*(7/50 : ℝ)=(10001841024999099/10000000000000000 : ℝ) by norm_num, show 1+2*(37004273789425349/100000000000000000000 : ℝ)=(50037004273789425349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27979896077942262101/27990000000000000000 : ℝ)*(X 1 0+X 2 0)+(272445554111/139950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (7/50 : ℝ)) (c := (27979896077942262101/27990000000000000000 : ℝ)) (alpha := (272445554111/139950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27979896077942262101/27990000000000000000 : ℝ)*(X 0 1+X 2 1)+(272445554111/139950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (7/50 : ℝ)) (c := (27979896077942262101/27990000000000000000 : ℝ)) (alpha := (272445554111/139950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27979896077942262101/27990000000000000000 : ℝ)*(X 0 2+X 1 2)+(272445554111/139950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (7/50 : ℝ)) (c := (27979896077942262101/27990000000000000000 : ℝ)) (alpha := (272445554111/139950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1108559669/5000000000 : ℝ)*X 0 0+(2697473719/5000000000 : ℝ)*X 0 1+(5263832381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672532863/5000000000 : ℝ)*X 1 0+(-2283652423/10000000000 : ℝ)*X 1 1+(2631916097/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672532833/5000000000 : ℝ)*X 2 0+(5263832337/10000000000 : ℝ)*X 2 1+(-1141826157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379383637/10000000000 : ℝ)*X 0 0+(4253489267/10000000000 : ℝ)*X 0 1+(36072643/80000000 : ℝ)*X 0 2+(4379383637/10000000000 : ℝ)*X 1 0+(4253489267/10000000000 : ℝ)*X 1 1+(36072643/80000000 : ℝ)*X 1 2+(4379383637/10000000000 : ℝ)*X 2 0+(4253489267/10000000000 : ℝ)*X 2 1+(36072643/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-110856227/500000000 : ℝ)*X 0 0+(658020119/1250000000 : ℝ)*X 0 1+(5394617651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312111967/10000000000 : ℝ)*X 1 0+(-1076433519/5000000000 : ℝ)*X 1 1+(2697308817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312112007/10000000000 : ℝ)*X 2 0+(5394617609/10000000000 : ℝ)*X 2 1+(-2152867017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379393559/10000000000 : ℝ)*X 0 0+(4508439689/10000000000 : ℝ)*X 0 1+(850826481/2000000000 : ℝ)*X 0 2+(4379393559/10000000000 : ℝ)*X 1 0+(4508439689/10000000000 : ℝ)*X 1 1+(850826481/2000000000 : ℝ)*X 1 2+(4379393559/10000000000 : ℝ)*X 2 0+(4508439689/10000000000 : ℝ)*X 2 1+(850826481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1412291202006078713272627287/155500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1691949421/100000000000000 : ℝ)*(base19) + (660418577/50000000000000 : ℝ)*(base23) + (7630009/5000000000000 : ℝ)*(lower2) + (44178641/25000000000000 : ℝ)*(upper3) + (117154119/100000000000000 : ℝ)*(upper5) + (5769753089323761/100000000000000 : ℝ)*(major0) + (5769753089323761/100000000000000 : ℝ)*(major1) + (5769753089323761/100000000000000 : ℝ)*(major2) + (7626925231550673/100000000000000 : ℝ)*(sp0) + (7626960393666013/100000000000000 : ℝ)*(sp1) + (7626960764778281/100000000000000 : ℝ)*(sp2) + (1956260145833129/50000000000000 : ℝ)*(sp3) + (36854064761/100000000000000 : ℝ)*(sp4) + (5874655967/25000000000000 : ℝ)*(sp7) + (1956271895145063/50000000000000 : ℝ)*(f.failure) + (1525392417123087/20000000000000 : ℝ)*(f.sum) + (5937916403741/777500000000000000000000000 : ℝ)*base66 + (313463808445857571/311000000000000000000000000000000 : ℝ)*base68 + (3236514133324142429/311000000000000000000000000000000 : ℝ)*base69 + (4828744291022142429/311000000000000000000000000000000 : ℝ)*base71 + (14126249481207/1555000000000000000000000000 : ℝ)*base74 + (1971362396753857571/311000000000000000000000000000000 : ℝ)*base76 + (862005148165857571/311000000000000000000000000000000 : ℝ)*base78 + (6147554622706857571/311000000000000000000000000000000 : ℝ)*base80 + (670042835321/777500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (26653851/5000000000000000000000 : ℝ)*base89 + (26653851/5000000000000000000000 : ℝ)*base91 + (26653851/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221224591607990472196157181/77750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145461919/100000000000000 : ℝ)*(base19) + (130252313/50000000000000 : ℝ)*(base23) + (9507253/100000000000000 : ℝ)*(upper3) + (10491303/50000000000000 : ℝ)*(lower4) + (6229093/100000000000000 : ℝ)*(upper5) + (2899407448431243/50000000000000 : ℝ)*(major0) + (2899407448431243/50000000000000 : ℝ)*(major1) + (2899407448431243/50000000000000 : ℝ)*(major2) + (1699439051/50000000000000 : ℝ)*(sp1) + (783996237/12500000000000 : ℝ)*(sp2) + (119771542547747/1562500000000 : ℝ)*(sp4) + (3832687589357893/50000000000000 : ℝ)*(sp5) + (3832686095290643/50000000000000 : ℝ)*(sp6) + (786450195164949/20000000000000 : ℝ)*(sp7) + (786450195164949/20000000000000 : ℝ)*(f.failure) + (119771542547747/1562500000000 : ℝ)*(f.sum) + (4220080835063/1555000000000000000000000000 : ℝ)*base65 + (1048106565717964273/155500000000000000000000000000000 : ℝ)*base68 + (476506481183964273/155500000000000000000000000000000 : ℝ)*base70 + (341496318318035727/155500000000000000000000000000000 : ℝ)*base71 + (3000114067517/1555000000000000000000000000 : ℝ)*base74 + (2797207001855964273/155500000000000000000000000000000 : ℝ)*base76 + (1308475092713964273/155500000000000000000000000000000 : ℝ)*base78 + (807570891777035727/155500000000000000000000000000000 : ℝ)*base79 + (8853530842943/1555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6833073/2000000000000000000000 : ℝ)*base89 + (6833073/2000000000000000000000 : ℝ)*base91 + (6833073/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1039_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7/50 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1039_s8_0 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217135231/10000000000 : ℝ)*x 0 + (5394824717/10000000000 : ℝ)*x 1 + (5263944169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217135231/10000000000 : ℝ)^1029 ≤ (13462739717577/100000000000000 : ℝ)^773 := by
    have hnat : (2217135231 : ℕ)^1029*100000000000000^773 ≤ 13462739717577^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217135231 10000000000 13462739717577 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394824717/10000000000 : ℝ)^1029 ≤ (43975859418157/100000000000000 : ℝ)^773 := by
    have hnat : (5394824717 : ℕ)^1029*100000000000000^773 ≤ 43975859418157^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394824717 10000000000 43975859418157 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263944169/10000000000 : ℝ)^1029 ≤ (42561400851941/100000000000000 : ℝ)^773 := by
    have hnat : (5263944169 : ℕ)^1029*100000000000000^773 ≤ 42561400851941^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263944169 10000000000 42561400851941 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217135231/10000000000 : ℝ), (5394824717/10000000000 : ℝ), (5263944169/10000000000 : ℝ)] ![(13462739717577/100000000000000 : ℝ), (43975859418157/100000000000000 : ℝ), (42561400851941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217135231/10000000000 : ℝ)|^1029 ≤ (13462739717577/100000000000000 : ℝ)^773
        have hw : |(-2217135231/10000000000 : ℝ)|=(2217135231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394824717/10000000000 : ℝ)|^1029 ≤ (43975859418157/100000000000000 : ℝ)^773
        have hw : |(5394824717/10000000000 : ℝ)|=(5394824717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263944169/10000000000 : ℝ)|^1029 ≤ (42561400851941/100000000000000 : ℝ)^773
        have hw : |(5263944169/10000000000 : ℝ)|=(5263944169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_1 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (42760269/80000000 : ℝ)*x 0 + (-2283547317/10000000000 : ℝ)*x 1 + (5263944169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42760269/80000000 : ℝ)^1029 ≤ (43436399823377/100000000000000 : ℝ)^773 := by
    have hnat : (42760269 : ℕ)^1029*100000000000000^773 ≤ 43436399823377^773*80000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42760269 80000000 43436399823377 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283547317/10000000000 : ℝ)^1029 ≤ (14002199316291/100000000000000 : ℝ)^773 := by
    have hnat : (2283547317 : ℕ)^1029*100000000000000^773 ≤ 14002199316291^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283547317 10000000000 14002199316291 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263944169/10000000000 : ℝ)^1029 ≤ (42561400851941/100000000000000 : ℝ)^773 := by
    have hnat : (5263944169 : ℕ)^1029*100000000000000^773 ≤ 42561400851941^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263944169 10000000000 42561400851941 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42760269/80000000 : ℝ), (-2283547317/10000000000 : ℝ), (5263944169/10000000000 : ℝ)] ![(43436399823377/100000000000000 : ℝ), (14002199316291/100000000000000 : ℝ), (42561400851941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42760269/80000000 : ℝ)|^1029 ≤ (43436399823377/100000000000000 : ℝ)^773
        have hw : |(42760269/80000000 : ℝ)|=(42760269/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2283547317/10000000000 : ℝ)|^1029 ≤ (14002199316291/100000000000000 : ℝ)^773
        have hw : |(-2283547317/10000000000 : ℝ)|=(2283547317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263944169/10000000000 : ℝ)|^1029 ≤ (42561400851941/100000000000000 : ℝ)^773
        have hw : |(5263944169/10000000000 : ℝ)|=(5263944169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_2 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (42760269/80000000 : ℝ)*x 0 + (5263944169/10000000000 : ℝ)*x 1 + (-2283547317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42760269/80000000 : ℝ)^1029 ≤ (43436399823377/100000000000000 : ℝ)^773 := by
    have hnat : (42760269 : ℕ)^1029*100000000000000^773 ≤ 43436399823377^773*80000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42760269 80000000 43436399823377 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263944169/10000000000 : ℝ)^1029 ≤ (42561400851941/100000000000000 : ℝ)^773 := by
    have hnat : (5263944169 : ℕ)^1029*100000000000000^773 ≤ 42561400851941^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263944169 10000000000 42561400851941 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283547317/10000000000 : ℝ)^1029 ≤ (14002199316291/100000000000000 : ℝ)^773 := by
    have hnat : (2283547317 : ℕ)^1029*100000000000000^773 ≤ 14002199316291^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283547317 10000000000 14002199316291 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42760269/80000000 : ℝ), (5263944169/10000000000 : ℝ), (-2283547317/10000000000 : ℝ)] ![(43436399823377/100000000000000 : ℝ), (42561400851941/100000000000000 : ℝ), (14002199316291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42760269/80000000 : ℝ)|^1029 ≤ (43436399823377/100000000000000 : ℝ)^773
        have hw : |(42760269/80000000 : ℝ)|=(42760269/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263944169/10000000000 : ℝ)|^1029 ≤ (42561400851941/100000000000000 : ℝ)^773
        have hw : |(5263944169/10000000000 : ℝ)|=(5263944169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283547317/10000000000 : ℝ)|^1029 ≤ (14002199316291/100000000000000 : ℝ)^773
        have hw : |(-2283547317/10000000000 : ℝ)|=(2283547317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_3 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (547423703/1250000000 : ℝ)*x 0 + (4253717283/10000000000 : ℝ)*x 1 + (450885079/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547423703/1250000000 : ℝ)^1029 ≤ (4164548669687/12500000000000 : ℝ)^773 := by
    have hnat : (547423703 : ℕ)^1029*12500000000000^773 ≤ 4164548669687^773*1250000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547423703 1250000000 4164548669687 12500000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253717283/10000000000 : ℝ)^1029 ≤ (6409958788861/20000000000000 : ℝ)^773 := by
    have hnat : (4253717283 : ℕ)^1029*20000000000000^773 ≤ 6409958788861^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253717283 10000000000 6409958788861 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450885079/1000000000 : ℝ)^1029 ≤ (2164613543039/6250000000000 : ℝ)^773 := by
    have hnat : (450885079 : ℕ)^1029*6250000000000^773 ≤ 2164613543039^773*1000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450885079 1000000000 2164613543039 6250000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547423703/1250000000 : ℝ), (4253717283/10000000000 : ℝ), (450885079/1000000000 : ℝ)] ![(4164548669687/12500000000000 : ℝ), (6409958788861/20000000000000 : ℝ), (2164613543039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547423703/1250000000 : ℝ)|^1029 ≤ (4164548669687/12500000000000 : ℝ)^773
        have hw : |(547423703/1250000000 : ℝ)|=(547423703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253717283/10000000000 : ℝ)|^1029 ≤ (6409958788861/20000000000000 : ℝ)^773
        have hw : |(4253717283/10000000000 : ℝ)|=(4253717283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450885079/1000000000 : ℝ)|^1029 ≤ (2164613543039/6250000000000 : ℝ)^773
        have hw : |(450885079/1000000000 : ℝ)|=(450885079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_4 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-110857011/500000000 : ℝ)*x 0 + (5264271833/10000000000 : ℝ)*x 1 + (337155999/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110857011/500000000 : ℝ)^1029 ≤ (13462780044103/100000000000000 : ℝ)^773 := by
    have hnat : (110857011 : ℕ)^1029*100000000000000^773 ≤ 13462780044103^773*500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110857011 500000000 13462780044103 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264271833/10000000000 : ℝ)^1029 ≤ (10641231898557/25000000000000 : ℝ)^773 := by
    have hnat : (5264271833 : ℕ)^1029*25000000000000^773 ≤ 10641231898557^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264271833 10000000000 10641231898557 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337155999/625000000 : ℝ)^1029 ≤ (43972292346787/100000000000000 : ℝ)^773 := by
    have hnat : (337155999 : ℕ)^1029*100000000000000^773 ≤ 43972292346787^773*625000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337155999 625000000 43972292346787 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110857011/500000000 : ℝ), (5264271833/10000000000 : ℝ), (337155999/625000000 : ℝ)] ![(13462780044103/100000000000000 : ℝ), (10641231898557/25000000000000 : ℝ), (43972292346787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110857011/500000000 : ℝ)|^1029 ≤ (13462780044103/100000000000000 : ℝ)^773
        have hw : |(-110857011/500000000 : ℝ)|=(110857011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264271833/10000000000 : ℝ)|^1029 ≤ (10641231898557/25000000000000 : ℝ)^773
        have hw : |(5264271833/10000000000 : ℝ)|=(5264271833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337155999/625000000 : ℝ)|^1029 ≤ (43972292346787/100000000000000 : ℝ)^773
        have hw : |(337155999/625000000 : ℝ)|=(337155999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_5 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656069451/5000000000 : ℝ)*x 0 + (-215299601/1000000000 : ℝ)*x 1 + (5394495691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656069451/5000000000 : ℝ)^1029 ≤ (43080914167707/100000000000000 : ℝ)^773 := by
    have hnat : (2656069451 : ℕ)^1029*100000000000000^773 ≤ 43080914167707^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656069451 5000000000 43080914167707 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215299601/1000000000 : ℝ)^1029 ≤ (3236699161599/25000000000000 : ℝ)^773 := by
    have hnat : (215299601 : ℕ)^1029*25000000000000^773 ≤ 3236699161599^773*1000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215299601 1000000000 3236699161599 25000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394495691/10000000000 : ℝ)^1029 ≤ (21986144583743/50000000000000 : ℝ)^773 := by
    have hnat : (5394495691 : ℕ)^1029*50000000000000^773 ≤ 21986144583743^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394495691 10000000000 21986144583743 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656069451/5000000000 : ℝ), (-215299601/1000000000 : ℝ), (5394495691/10000000000 : ℝ)] ![(43080914167707/100000000000000 : ℝ), (3236699161599/25000000000000 : ℝ), (21986144583743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656069451/5000000000 : ℝ)|^1029 ≤ (43080914167707/100000000000000 : ℝ)^773
        have hw : |(2656069451/5000000000 : ℝ)|=(2656069451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215299601/1000000000 : ℝ)|^1029 ≤ (3236699161599/25000000000000 : ℝ)^773
        have hw : |(-215299601/1000000000 : ℝ)|=(215299601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394495691/10000000000 : ℝ)|^1029 ≤ (21986144583743/50000000000000 : ℝ)^773
        have hw : |(5394495691/10000000000 : ℝ)|=(5394495691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_6 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656069793/5000000000 : ℝ)*x 0 + (5394495771/10000000000 : ℝ)*x 1 + (-2152994979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656069793/5000000000 : ℝ)^1029 ≤ (1723236862079/4000000000000 : ℝ)^773 := by
    have hnat : (2656069793 : ℕ)^1029*4000000000000^773 ≤ 1723236862079^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656069793 5000000000 1723236862079 4000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394495771/10000000000 : ℝ)^1029 ≤ (8794458007111/20000000000000 : ℝ)^773 := by
    have hnat : (5394495771 : ℕ)^1029*20000000000000^773 ≤ 8794458007111^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394495771 10000000000 8794458007111 20000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152994979/10000000000 : ℝ)^1029 ≤ (6473394196681/50000000000000 : ℝ)^773 := by
    have hnat : (2152994979 : ℕ)^1029*50000000000000^773 ≤ 6473394196681^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152994979 10000000000 6473394196681 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656069793/5000000000 : ℝ), (5394495771/10000000000 : ℝ), (-2152994979/10000000000 : ℝ)] ![(1723236862079/4000000000000 : ℝ), (8794458007111/20000000000000 : ℝ), (6473394196681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656069793/5000000000 : ℝ)|^1029 ≤ (1723236862079/4000000000000 : ℝ)^773
        have hw : |(2656069793/5000000000 : ℝ)|=(2656069793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394495771/10000000000 : ℝ)|^1029 ≤ (8794458007111/20000000000000 : ℝ)^773
        have hw : |(5394495771/10000000000 : ℝ)|=(5394495771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152994979/10000000000 : ℝ)|^1029 ≤ (6473394196681/50000000000000 : ℝ)^773
        have hw : |(-2152994979/10000000000 : ℝ)|=(2152994979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1039_s8_7 (p : ℝ) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1094849897/2500000000 : ℝ)*x 0 + (2254106353/5000000000 : ℝ)*x 1 + (4254357703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094849897/2500000000 : ℝ)^1029 ≤ (16658245131413/50000000000000 : ℝ)^773 := by
    have hnat : (1094849897 : ℕ)^1029*50000000000000^773 ≤ 16658245131413^773*2500000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094849897 2500000000 16658245131413 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254106353/5000000000 : ℝ)^1029 ≤ (34627292326641/100000000000000 : ℝ)^773 := by
    have hnat : (2254106353 : ℕ)^1029*100000000000000^773 ≤ 34627292326641^773*5000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254106353 5000000000 34627292326641 100000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254357703/10000000000 : ℝ)^1029 ≤ (16028108696159/50000000000000 : ℝ)^773 := by
    have hnat : (4254357703 : ℕ)^1029*50000000000000^773 ≤ 16028108696159^773*10000000000^1029 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254357703 10000000000 16028108696159 50000000000000 1029 773 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1029/256 : ℝ)) 1029 773 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094849897/2500000000 : ℝ), (2254106353/5000000000 : ℝ), (4254357703/10000000000 : ℝ)] ![(16658245131413/50000000000000 : ℝ), (34627292326641/100000000000000 : ℝ), (16028108696159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094849897/2500000000 : ℝ)|^1029 ≤ (16658245131413/50000000000000 : ℝ)^773
        have hw : |(1094849897/2500000000 : ℝ)|=(1094849897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254106353/5000000000 : ℝ)|^1029 ≤ (34627292326641/100000000000000 : ℝ)^773
        have hw : |(2254106353/5000000000 : ℝ)|=(2254106353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254357703/10000000000 : ℝ)|^1029 ≤ (16028108696159/50000000000000 : ℝ)^773
        have hw : |(4254357703/10000000000 : ℝ)|=(4254357703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1039_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6993/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (8231/2048 : ℝ) ≤ (7576171928966899/50000000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^8231 ≤ (7576171928966899/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11211 : ℕ)^8231*50000000000000000000^2048 ≤ 7576171928966899^2048*100000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 7576171928966899 50000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (7576171928966899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3497/25000 : ℝ) ^ (8231/2048 : ℝ) ≤ (36876962832359729/100000000000000000000 : ℝ) := by
    have hpowers : (3497/25000 : ℝ)^8231 ≤ (36876962832359729/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3497 : ℕ)^8231*100000000000000000000^2048 ≤ 36876962832359729^2048*25000^8231 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3497 25000 36876962832359729 100000000000000000000 8231 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3497/25000 : ℝ)) (X := (36876962832359729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007576171928966899/25000000000000000000 : ℝ) ≤ (5000376970826381/5000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (25007576171928966899/25000000000000000000 : ℝ)^2048 ≤ (5000376970826381/5000000000000000 : ℝ)^8231 := by
      have hnat : (25007576171928966899 : ℕ)^2048*5000000000000000^8231 ≤ 5000376970826381^8231*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007576171928966899 25000000000000000000 5000376970826381 5000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000376970826381/5000000000000000 : ℝ)) (X := (25007576171928966899/25000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052029306690293527/100000000000000000000 : ℝ) ≤ (10001294316649901/10000000000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (100052029306690293527/100000000000000000000 : ℝ)^2048 ≤ (10001294316649901/10000000000000000 : ℝ)^8231 := by
      have hnat : (100052029306690293527 : ℕ)^2048*10000000000000000^8231 ≤ 10001294316649901^8231*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052029306690293527 100000000000000000000 10001294316649901 10000000000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001294316649901/10000000000000000 : ℝ)) (X := (100052029306690293527/100000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036876962832359729/50000000000000000000 : ℝ) ≤ (31255733411397/31250000000000 : ℝ) ^ (8231/2048 : ℝ) := by
    have hpowers : (50036876962832359729/50000000000000000000 : ℝ)^2048 ≤ (31255733411397/31250000000000 : ℝ)^8231 := by
      have hnat : (50036876962832359729 : ℕ)^2048*31250000000000^8231 ≤ 31255733411397^8231*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036876962832359729 50000000000000000000 31255733411397 31250000000000 2048 8231 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31255733411397/31250000000000 : ℝ)) (X := (50036876962832359729/50000000000000000000 : ℝ)) (by norm_num) 8231 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7576171928966899/50000000000000000000 : ℝ) ≤ ((3469997175972983677/3471250000000000000 : ℝ)+2*(540374997139/277700000000000 : ℝ)*(11211/100000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (3469997175972983677/3471250000000000000 : ℝ)+2*(540374997139/277700000000000 : ℝ)*(11211/100000 : ℝ)=(5000376970826381/5000000000000000 : ℝ) by norm_num, show 1+2*(7576171928966899/50000000000000000000 : ℝ)=(25007576171928966899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36876962832359729/100000000000000000000 : ℝ)+(7576171928966899/50000000000000000000 : ℝ) ≤ ((3469997175972983677/3471250000000000000 : ℝ)+(540374997139/277700000000000 : ℝ)*((3497/25000 : ℝ)+(11211/100000 : ℝ)))^(8231/2048 : ℝ) := by
    rw [show (3469997175972983677/3471250000000000000 : ℝ)+(540374997139/277700000000000 : ℝ)*((3497/25000 : ℝ)+(11211/100000 : ℝ))=(10001294316649901/10000000000000000 : ℝ) by norm_num, show 1+(36876962832359729/100000000000000000000 : ℝ)+(7576171928966899/50000000000000000000 : ℝ)=(100052029306690293527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36876962832359729/100000000000000000000 : ℝ) ≤ ((3469997175972983677/3471250000000000000 : ℝ)+2*(540374997139/277700000000000 : ℝ)*(3497/25000 : ℝ))^(8231/2048 : ℝ) := by
    rw [show (3469997175972983677/3471250000000000000 : ℝ)+2*(540374997139/277700000000000 : ℝ)*(3497/25000 : ℝ)=(31255733411397/31250000000000 : ℝ) by norm_num, show 1+2*(36876962832359729/100000000000000000000 : ℝ)=(50036876962832359729/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3469997175972983677/3471250000000000000 : ℝ)*(X 1 0+X 2 0)+(540374997139/277700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (3469997175972983677/3471250000000000000 : ℝ)) (alpha := (540374997139/277700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3469997175972983677/3471250000000000000 : ℝ)*(X 0 1+X 2 1)+(540374997139/277700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (3469997175972983677/3471250000000000000 : ℝ)) (alpha := (540374997139/277700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3469997175972983677/3471250000000000000 : ℝ)*(X 0 2+X 1 2)+(540374997139/277700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8231/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (3469997175972983677/3471250000000000000 : ℝ)) (alpha := (540374997139/277700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2217135231/10000000000 : ℝ)*X 0 0+(5394824717/10000000000 : ℝ)*X 0 1+(5263944169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42760269/80000000 : ℝ)*X 1 0+(-2283547317/10000000000 : ℝ)*X 1 1+(5263944169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42760269/80000000 : ℝ)*X 2 0+(5263944169/10000000000 : ℝ)*X 2 1+(-2283547317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547423703/1250000000 : ℝ)*X 0 0+(4253717283/10000000000 : ℝ)*X 0 1+(450885079/1000000000 : ℝ)*X 0 2+(547423703/1250000000 : ℝ)*X 1 0+(4253717283/10000000000 : ℝ)*X 1 1+(450885079/1000000000 : ℝ)*X 1 2+(547423703/1250000000 : ℝ)*X 2 0+(4253717283/10000000000 : ℝ)*X 2 1+(450885079/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-110857011/500000000 : ℝ)*X 0 0+(5264271833/10000000000 : ℝ)*X 0 1+(337155999/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656069451/5000000000 : ℝ)*X 1 0+(-215299601/1000000000 : ℝ)*X 1 1+(5394495691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656069793/5000000000 : ℝ)*X 2 0+(5394495771/10000000000 : ℝ)*X 2 1+(-2152994979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094849897/2500000000 : ℝ)*X 0 0+(2254106353/5000000000 : ℝ)*X 0 1+(4254357703/10000000000 : ℝ)*X 0 2+(1094849897/2500000000 : ℝ)*X 1 0+(2254106353/5000000000 : ℝ)*X 1 1+(4254357703/10000000000 : ℝ)*X 1 2+(1094849897/2500000000 : ℝ)*X 2 0+(2254106353/5000000000 : ℝ)*X 2 1+(4254357703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1039_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128158885126212860224847217/43390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599667823/100000000000000 : ℝ)*(base19) + (278796879/50000000000000 : ℝ)*(base23) + (2811091/12500000000000 : ℝ)*(lower2) + (3019791/4000000000000 : ℝ)*(upper3) + (22044281/50000000000000 : ℝ)*(upper5) + (722507564612191/12500000000000 : ℝ)*(major0) + (722507564612191/12500000000000 : ℝ)*(major1) + (722507564612191/12500000000000 : ℝ)*(major2) + (764057157428953/10000000000000 : ℝ)*(sp0) + (7640586946153999/100000000000000 : ℝ)*(sp1) + (238768343382127/3125000000000 : ℝ)*(sp2) + (783904902832127/20000000000000 : ℝ)*(sp3) + (15971532293/100000000000000 : ℝ)*(sp4) + (4437679501/50000000000000 : ℝ)*(sp7) + (3919533389519637/100000000000000 : ℝ)*(f.failure) + (3820293772910911/50000000000000 : ℝ)*(f.sum) + (10460128870559/6942500000000000000000000000 : ℝ)*base66 + (197896167849256307/43390625000000000000000000000000 : ℝ)*base67 + (335880363330962443/43390625000000000000000000000000 : ℝ)*base70 + (4734321355966163/677978515625000000000000000000 : ℝ)*base71 + (13992904945651/6942500000000000000000000000 : ℝ)*base73 + (70926700491317571/5423828125000000000000000000000 : ℝ)*base76 + (224869288384181193/43390625000000000000000000000000 : ℝ)*base78 + (141584433892942159/21695312500000000000000000000000 : ℝ)*base80 + (2057988124607/867812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (22128049/10000000000000000000000 : ℝ)*base89 + (22128049/10000000000000000000000 : ℝ)*base91 + (22128049/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (542159908202463128454058581/86781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104639391/12500000000000 : ℝ)*(base19) + (2597131299/100000000000000 : ℝ)*(base23) + (31186679/25000000000000 : ℝ)*(upper3) + (140834071/100000000000000 : ℝ)*(lower4) + (2904587141679517/50000000000000 : ℝ)*(major0) + (2904587141679517/50000000000000 : ℝ)*(major1) + (2904587141679517/50000000000000 : ℝ)*(major2) + (2741461063/100000000000000 : ℝ)*(sp1) + (84477477227/100000000000000 : ℝ)*(sp2) + (5087076701/100000000000000 : ℝ)*(sp3) + (7679072549402157/100000000000000 : ℝ)*(sp4) + (3839534485412983/50000000000000 : ℝ)*(sp5) + (239968296087301/3125000000000 : ℝ)*(sp6) + (1969635360995739/50000000000000 : ℝ)*(sp7) + (1969637904534089/50000000000000 : ℝ)*(f.failure) + (7679072549402157/100000000000000 : ℝ)*(f.sum) + (50305092334627/6942500000000000000000000000 : ℝ)*base66 + (1444069562136968491/173562500000000000000000000000000 : ℝ)*base68 + (2326157522221968491/173562500000000000000000000000000 : ℝ)*base70 + (2327580367290155991/173562500000000000000000000000000 : ℝ)*base72 + (40258060957987/6942500000000000000000000000 : ℝ)*base74 + (1958181880266030991/173562500000000000000000000000000 : ℝ)*base76 + (5936135924855155991/173562500000000000000000000000000 : ℝ)*base78 + (10076048780671843491/173562500000000000000000000000000 : ℝ)*base80 + (41150007473519/13885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14223147/5000000000000000000000 : ℝ)*base90 + (14223147/5000000000000000000000 : ℝ)*base92 + (14223147/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1039_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1039_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1039_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1039_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1039_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1039_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8231/2048 : ℝ) ≤ p) (hpb : p ≤ (1029/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147468077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6993/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1039_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
