-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:55:13.851983+00:00
-- url     : https://prove2.me/submissions/2eb972ed-e742-4e53-80fd-800020ed3123

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
theorem support_rectangle_w1051_s6_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211121339/10000000000 : ℝ)*x 0 + (5395228643/10000000000 : ℝ)*x 1 + (2631799433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211121339/10000000000 : ℝ)^2061 ≤ (13427141013341/100000000000000 : ℝ)^1549 := by
    have hnat : (2211121339 : ℕ)^2061*100000000000000^1549 ≤ 13427141013341^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211121339 10000000000 13427141013341 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395228643/10000000000 : ℝ)^2061 ≤ (1374926652829/3125000000000 : ℝ)^1549 := by
    have hnat : (5395228643 : ℕ)^2061*3125000000000^1549 ≤ 1374926652829^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395228643 10000000000 1374926652829 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631799433/5000000000 : ℝ)^2061 ≤ (42575206072119/100000000000000 : ℝ)^1549 := by
    have hnat : (2631799433 : ℕ)^2061*100000000000000^1549 ≤ 42575206072119^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631799433 5000000000 42575206072119 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211121339/10000000000 : ℝ), (5395228643/10000000000 : ℝ), (2631799433/5000000000 : ℝ)] ![(13427141013341/100000000000000 : ℝ), (1374926652829/3125000000000 : ℝ), (42575206072119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211121339/10000000000 : ℝ)|^2061 ≤ (13427141013341/100000000000000 : ℝ)^1549
        have hw : |(-2211121339/10000000000 : ℝ)|=(2211121339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395228643/10000000000 : ℝ)|^2061 ≤ (1374926652829/3125000000000 : ℝ)^1549
        have hw : |(5395228643/10000000000 : ℝ)|=(5395228643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631799433/5000000000 : ℝ)|^2061 ≤ (42575206072119/100000000000000 : ℝ)^1549
        have hw : |(2631799433/5000000000 : ℝ)|=(2631799433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069032841/2000000000 : ℝ)*x 0 + (-1138959523/5000000000 : ℝ)*x 1 + (2631799433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069032841/2000000000 : ℝ)^2061 ≤ (173821071671/400000000000 : ℝ)^1549 := by
    have hnat : (1069032841 : ℕ)^2061*400000000000^1549 ≤ 173821071671^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069032841 2000000000 173821071671 400000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138959523/5000000000 : ℝ)^2061 ≤ (13969525994429/100000000000000 : ℝ)^1549 := by
    have hnat : (1138959523 : ℕ)^2061*100000000000000^1549 ≤ 13969525994429^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138959523 5000000000 13969525994429 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631799433/5000000000 : ℝ)^2061 ≤ (42575206072119/100000000000000 : ℝ)^1549 := by
    have hnat : (2631799433 : ℕ)^2061*100000000000000^1549 ≤ 42575206072119^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631799433 5000000000 42575206072119 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069032841/2000000000 : ℝ), (-1138959523/5000000000 : ℝ), (2631799433/5000000000 : ℝ)] ![(173821071671/400000000000 : ℝ), (13969525994429/100000000000000 : ℝ), (42575206072119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069032841/2000000000 : ℝ)|^2061 ≤ (173821071671/400000000000 : ℝ)^1549
        have hw : |(1069032841/2000000000 : ℝ)|=(1069032841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138959523/5000000000 : ℝ)|^2061 ≤ (13969525994429/100000000000000 : ℝ)^1549
        have hw : |(-1138959523/5000000000 : ℝ)|=(1138959523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631799433/5000000000 : ℝ)|^2061 ≤ (42575206072119/100000000000000 : ℝ)^1549
        have hw : |(2631799433/5000000000 : ℝ)|=(2631799433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83518189/156250000 : ℝ)*x 0 + (5263598937/10000000000 : ℝ)*x 1 + (-2277919097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83518189/156250000 : ℝ)^2061 ≤ (21727633369347/50000000000000 : ℝ)^1549 := by
    have hnat : (83518189 : ℕ)^2061*50000000000000^1549 ≤ 21727633369347^1549*156250000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83518189 156250000 21727633369347 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263598937/10000000000 : ℝ)^2061 ≤ (8515041367247/20000000000000 : ℝ)^1549 := by
    have hnat : (5263598937 : ℕ)^2061*20000000000000^1549 ≤ 8515041367247^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263598937 10000000000 8515041367247 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277919097/10000000000 : ℝ)^2061 ≤ (1396952641057/10000000000000 : ℝ)^1549 := by
    have hnat : (2277919097 : ℕ)^2061*10000000000000^1549 ≤ 1396952641057^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277919097 10000000000 1396952641057 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83518189/156250000 : ℝ), (5263598937/10000000000 : ℝ), (-2277919097/10000000000 : ℝ)] ![(21727633369347/50000000000000 : ℝ), (8515041367247/20000000000000 : ℝ), (1396952641057/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83518189/156250000 : ℝ)|^2061 ≤ (21727633369347/50000000000000 : ℝ)^1549
        have hw : |(83518189/156250000 : ℝ)|=(83518189/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263598937/10000000000 : ℝ)|^2061 ≤ (8515041367247/20000000000000 : ℝ)^1549
        have hw : |(5263598937/10000000000 : ℝ)|=(5263598937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2277919097/10000000000 : ℝ)|^2061 ≤ (1396952641057/10000000000000 : ℝ)^1549
        have hw : |(-2277919097/10000000000 : ℝ)|=(2277919097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2188811751/5000000000 : ℝ)*x 0 + (4250939981/10000000000 : ℝ)*x 1 + (4508148153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188811751/5000000000 : ℝ)^2061 ≤ (33316152905867/100000000000000 : ℝ)^1549 := by
    have hnat : (2188811751 : ℕ)^2061*100000000000000^1549 ≤ 33316152905867^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188811751 5000000000 33316152905867 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250939981/10000000000 : ℝ)^2061 ≤ (6407903181887/20000000000000 : ℝ)^1549 := by
    have hnat : (4250939981 : ℕ)^2061*20000000000000^1549 ≤ 6407903181887^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250939981 10000000000 6407903181887 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508148153/10000000000 : ℝ)^2061 ≤ (17322165583301/50000000000000 : ℝ)^1549 := by
    have hnat : (4508148153 : ℕ)^2061*50000000000000^1549 ≤ 17322165583301^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508148153 10000000000 17322165583301 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188811751/5000000000 : ℝ), (4250939981/10000000000 : ℝ), (4508148153/10000000000 : ℝ)] ![(33316152905867/100000000000000 : ℝ), (6407903181887/20000000000000 : ℝ), (17322165583301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188811751/5000000000 : ℝ)|^2061 ≤ (33316152905867/100000000000000 : ℝ)^1549
        have hw : |(2188811751/5000000000 : ℝ)|=(2188811751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250939981/10000000000 : ℝ)|^2061 ≤ (6407903181887/20000000000000 : ℝ)^1549
        have hw : |(4250939981/10000000000 : ℝ)|=(4250939981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508148153/10000000000 : ℝ)|^2061 ≤ (17322165583301/50000000000000 : ℝ)^1549
        have hw : |(4508148153/10000000000 : ℝ)|=(4508148153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105563303/5000000000 : ℝ)*x 0 + (5263931347/10000000000 : ℝ)*x 1 + (5394894937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105563303/5000000000 : ℝ)^2061 ≤ (2685436713873/20000000000000 : ℝ)^1549 := by
    have hnat : (1105563303 : ℕ)^2061*20000000000000^1549 ≤ 2685436713873^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105563303 5000000000 2685436713873 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263931347/10000000000 : ℝ)^2061 ≤ (8515756866457/20000000000000 : ℝ)^1549 := by
    have hnat : (5263931347 : ℕ)^2061*20000000000000^1549 ≤ 8515756866457^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263931347 10000000000 8515756866457 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394894937/10000000000 : ℝ)^2061 ≤ (10998508019989/25000000000000 : ℝ)^1549 := by
    have hnat : (5394894937 : ℕ)^2061*25000000000000^1549 ≤ 10998508019989^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394894937 10000000000 10998508019989 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105563303/5000000000 : ℝ), (5263931347/10000000000 : ℝ), (5394894937/10000000000 : ℝ)] ![(2685436713873/20000000000000 : ℝ), (8515756866457/20000000000000 : ℝ), (10998508019989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105563303/5000000000 : ℝ)|^2061 ≤ (2685436713873/20000000000000 : ℝ)^1549
        have hw : |(-1105563303/5000000000 : ℝ)|=(1105563303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263931347/10000000000 : ℝ)|^2061 ≤ (8515756866457/20000000000000 : ℝ)^1549
        have hw : |(5263931347/10000000000 : ℝ)|=(5263931347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394894937/10000000000 : ℝ)|^2061 ≤ (10998508019989/25000000000000 : ℝ)^1549
        have hw : |(5394894937/10000000000 : ℝ)|=(5394894937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312049027/10000000000 : ℝ)*x 0 + (-268327877/1250000000 : ℝ)*x 1 + (2697447493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312049027/10000000000 : ℝ)^2061 ≤ (1723897095379/4000000000000 : ℝ)^1549 := by
    have hnat : (5312049027 : ℕ)^2061*4000000000000^1549 ≤ 1723897095379^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312049027 10000000000 1723897095379 4000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268327877/1250000000 : ℝ)^2061 ≤ (1290853998749/10000000000000 : ℝ)^1549 := by
    have hnat : (268327877 : ℕ)^2061*10000000000000^1549 ≤ 1290853998749^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268327877 1250000000 1290853998749 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697447493/5000000000 : ℝ)^2061 ≤ (1374813519113/3125000000000 : ℝ)^1549 := by
    have hnat : (2697447493 : ℕ)^2061*3125000000000^1549 ≤ 1374813519113^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697447493 5000000000 1374813519113 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312049027/10000000000 : ℝ), (-268327877/1250000000 : ℝ), (2697447493/5000000000 : ℝ)] ![(1723897095379/4000000000000 : ℝ), (1290853998749/10000000000000 : ℝ), (1374813519113/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312049027/10000000000 : ℝ)|^2061 ≤ (1723897095379/4000000000000 : ℝ)^1549
        have hw : |(5312049027/10000000000 : ℝ)|=(5312049027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-268327877/1250000000 : ℝ)|^2061 ≤ (1290853998749/10000000000000 : ℝ)^1549
        have hw : |(-268327877/1250000000 : ℝ)|=(268327877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697447493/5000000000 : ℝ)|^2061 ≤ (1374813519113/3125000000000 : ℝ)^1549
        have hw : |(2697447493/5000000000 : ℝ)|=(2697447493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41500383/78125000 : ℝ)*x 0 + (5394894981/10000000000 : ℝ)*x 1 + (-2146623027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41500383/78125000 : ℝ)^2061 ≤ (43097427352091/100000000000000 : ℝ)^1549 := by
    have hnat : (41500383 : ℕ)^2061*100000000000000^1549 ≤ 43097427352091^1549*78125000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41500383 78125000 43097427352091 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394894981/10000000000 : ℝ)^2061 ≤ (8798806511473/20000000000000 : ℝ)^1549 := by
    have hnat : (5394894981 : ℕ)^2061*20000000000000^1549 ≤ 8798806511473^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394894981 10000000000 8798806511473 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2146623027/10000000000 : ℝ)^2061 ≤ (12908540075501/100000000000000 : ℝ)^1549 := by
    have hnat : (2146623027 : ℕ)^2061*100000000000000^1549 ≤ 12908540075501^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146623027 10000000000 12908540075501 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41500383/78125000 : ℝ), (5394894981/10000000000 : ℝ), (-2146623027/10000000000 : ℝ)] ![(43097427352091/100000000000000 : ℝ), (8798806511473/20000000000000 : ℝ), (12908540075501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41500383/78125000 : ℝ)|^2061 ≤ (43097427352091/100000000000000 : ℝ)^1549
        have hw : |(41500383/78125000 : ℝ)|=(41500383/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394894981/10000000000 : ℝ)|^2061 ≤ (8798806511473/20000000000000 : ℝ)^1549
        have hw : |(5394894981/10000000000 : ℝ)|=(5394894981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2146623027/10000000000 : ℝ)|^2061 ≤ (12908540075501/100000000000000 : ℝ)^1549
        have hw : |(-2146623027/10000000000 : ℝ)|=(2146623027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s6_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4377633811/10000000000 : ℝ)*x 0 + (2253749169/5000000000 : ℝ)*x 1 + (132862253/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377633811/10000000000 : ℝ)^2061 ≤ (6663251459213/20000000000000 : ℝ)^1549 := by
    have hnat : (4377633811 : ℕ)^2061*20000000000000^1549 ≤ 6663251459213^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377633811 10000000000 6663251459213 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253749169/5000000000 : ℝ)^2061 ≤ (34637687008453/100000000000000 : ℝ)^1549 := by
    have hnat : (2253749169 : ℕ)^2061*100000000000000^1549 ≤ 34637687008453^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253749169 5000000000 34637687008453 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132862253/312500000 : ℝ)^2061 ≤ (32046055683529/100000000000000 : ℝ)^1549 := by
    have hnat : (132862253 : ℕ)^2061*100000000000000^1549 ≤ 32046055683529^1549*312500000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132862253 312500000 32046055683529 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377633811/10000000000 : ℝ), (2253749169/5000000000 : ℝ), (132862253/312500000 : ℝ)] ![(6663251459213/20000000000000 : ℝ), (34637687008453/100000000000000 : ℝ), (32046055683529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377633811/10000000000 : ℝ)|^2061 ≤ (6663251459213/20000000000000 : ℝ)^1549
        have hw : |(4377633811/10000000000 : ℝ)|=(4377633811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253749169/5000000000 : ℝ)|^2061 ≤ (34637687008453/100000000000000 : ℝ)^1549
        have hw : |(2253749169/5000000000 : ℝ)|=(2253749169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132862253/312500000 : ℝ)|^2061 ≤ (32046055683529/100000000000000 : ℝ)^1549
        have hw : |(132862253/312500000 : ℝ)|=(132862253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5609/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7003/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5587/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5587/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5587/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5587/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5587/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5587/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5587/50000 : ℝ) ^ (8243/2048 : ℝ) ≤ (461299362920767/3125000000000000000 : ℝ) := by
    have hpowers : (5587/50000 : ℝ)^8243 ≤ (461299362920767/3125000000000000000 : ℝ)^2048 := by
      have hnat : (5587 : ℕ)^8243*3125000000000000000^2048 ≤ 461299362920767^2048*50000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5587 50000 461299362920767 3125000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5587/50000 : ℝ)) (X := (461299362920767/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (3714100377885107/10000000000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^8243 ≤ (3714100377885107/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14053 : ℕ)^8243*10000000000000000000^2048 ≤ 3714100377885107^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 3714100377885107 10000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (3714100377885107/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562961299362920767/1562500000000000000 : ℝ) ≤ (5000366715536997/5000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (1562961299362920767/1562500000000000000 : ℝ)^2048 ≤ (5000366715536997/5000000000000000 : ℝ)^8243 := by
      have hnat : (1562961299362920767 : ℕ)^2048*5000000000000000^8243 ≤ 5000366715536997^8243*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562961299362920767 1562500000000000000 5000366715536997 5000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000366715536997/5000000000000000 : ℝ)) (X := (1562961299362920767/1562500000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025951291696157807/50000000000000000000 : ℝ) ≤ (250032232125869/250000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50025951291696157807/50000000000000000000 : ℝ)^2048 ≤ (250032232125869/250000000000000 : ℝ)^8243 := by
      have hnat : (50025951291696157807 : ℕ)^2048*250000000000000^8243 ≤ 250032232125869^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025951291696157807 50000000000000000000 250032232125869 250000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250032232125869/250000000000000 : ℝ)) (X := (50025951291696157807/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003714100377885107/5000000000000000000 : ℝ) ≤ (5000922569497763/5000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (5003714100377885107/5000000000000000000 : ℝ)^2048 ≤ (5000922569497763/5000000000000000 : ℝ)^8243 := by
      have hnat : (5003714100377885107 : ℕ)^2048*5000000000000000^8243 ≤ 5000922569497763^8243*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003714100377885107 5000000000000000000 5000922569497763 5000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000922569497763/5000000000000000 : ℝ)) (X := (5003714100377885107/5000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461299362920767/3125000000000000000 : ℝ) ≤ ((14389844661873415079/14395000000000000000 : ℝ)+2*(277926980383/143950000000000 : ℝ)*(5587/50000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (14389844661873415079/14395000000000000000 : ℝ)+2*(277926980383/143950000000000 : ℝ)*(5587/50000 : ℝ)=(5000366715536997/5000000000000000 : ℝ) by norm_num, show 1+2*(461299362920767/3125000000000000000 : ℝ)=(1562961299362920767/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3714100377885107/10000000000000000000 : ℝ)+(461299362920767/3125000000000000000 : ℝ) ≤ ((14389844661873415079/14395000000000000000 : ℝ)+(277926980383/143950000000000 : ℝ)*((14053/100000 : ℝ)+(5587/50000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (14389844661873415079/14395000000000000000 : ℝ)+(277926980383/143950000000000 : ℝ)*((14053/100000 : ℝ)+(5587/50000 : ℝ))=(250032232125869/250000000000000 : ℝ) by norm_num, show 1+(3714100377885107/10000000000000000000 : ℝ)+(461299362920767/3125000000000000000 : ℝ)=(50025951291696157807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3714100377885107/10000000000000000000 : ℝ) ≤ ((14389844661873415079/14395000000000000000 : ℝ)+2*(277926980383/143950000000000 : ℝ)*(14053/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (14389844661873415079/14395000000000000000 : ℝ)+2*(277926980383/143950000000000 : ℝ)*(14053/100000 : ℝ)=(5000922569497763/5000000000000000 : ℝ) by norm_num, show 1+2*(3714100377885107/10000000000000000000 : ℝ)=(5003714100377885107/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14389844661873415079/14395000000000000000 : ℝ)*(X 1 0+X 2 0)+(277926980383/143950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (5587/50000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (14389844661873415079/14395000000000000000 : ℝ)) (alpha := (277926980383/143950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14389844661873415079/14395000000000000000 : ℝ)*(X 0 1+X 2 1)+(277926980383/143950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (5587/50000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (14389844661873415079/14395000000000000000 : ℝ)) (alpha := (277926980383/143950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14389844661873415079/14395000000000000000 : ℝ)*(X 0 2+X 1 2)+(277926980383/143950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (5587/50000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (14389844661873415079/14395000000000000000 : ℝ)) (alpha := (277926980383/143950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2211121339/10000000000 : ℝ)*X 0 0+(5395228643/10000000000 : ℝ)*X 0 1+(2631799433/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069032841/2000000000 : ℝ)*X 1 0+(-1138959523/5000000000 : ℝ)*X 1 1+(2631799433/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83518189/156250000 : ℝ)*X 2 0+(5263598937/10000000000 : ℝ)*X 2 1+(-2277919097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188811751/5000000000 : ℝ)*X 0 0+(4250939981/10000000000 : ℝ)*X 0 1+(4508148153/10000000000 : ℝ)*X 0 2+(2188811751/5000000000 : ℝ)*X 1 0+(4250939981/10000000000 : ℝ)*X 1 1+(4508148153/10000000000 : ℝ)*X 1 2+(2188811751/5000000000 : ℝ)*X 2 0+(4250939981/10000000000 : ℝ)*X 2 1+(4508148153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1105563303/5000000000 : ℝ)*X 0 0+(5263931347/10000000000 : ℝ)*X 0 1+(5394894937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312049027/10000000000 : ℝ)*X 1 0+(-268327877/1250000000 : ℝ)*X 1 1+(2697447493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41500383/78125000 : ℝ)*X 2 0+(5394894981/10000000000 : ℝ)*X 2 1+(-2146623027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377633811/10000000000 : ℝ)*X 0 0+(2253749169/5000000000 : ℝ)*X 0 1+(132862253/312500000 : ℝ)*X 0 2+(4377633811/10000000000 : ℝ)*X 1 0+(2253749169/5000000000 : ℝ)*X 1 1+(132862253/312500000 : ℝ)*X 1 2+(4377633811/10000000000 : ℝ)*X 2 0+(2253749169/5000000000 : ℝ)*X 2 1+(132862253/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6407287716115593686165982579/719750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4691877/250000000000 : ℝ)*(base19) + (816543349/50000000000000 : ℝ)*(base23) + (47433369/100000000000000 : ℝ)*(lower2) + (70241861/25000000000000 : ℝ)*(upper3) + (52976731/50000000000000 : ℝ)*(upper5) + (5742560642244167/100000000000000 : ℝ)*(major0) + (5742560642244167/100000000000000 : ℝ)*(major1) + (5742560642244167/100000000000000 : ℝ)*(major2) + (3798559954344443/50000000000000 : ℝ)*(sp0) + (7597164334695803/100000000000000 : ℝ)*(sp1) + (237411393073747/3125000000000 : ℝ)*(sp2) + (485990802879889/12500000000000 : ℝ)*(sp3) + (46302757717/100000000000000 : ℝ)*(sp4) + (28353265883/100000000000000 : ℝ)*(sp7) + (1943977388152497/50000000000000 : ℝ)*(f.failure) + (7597166211446603/100000000000000 : ℝ)*(f.sum) + (116201044157073/14395000000000000000000000000 : ℝ)*base66 + (30967258022754805807/1439500000000000000000000000000000 : ℝ)*base68 + (16014663647001805807/1439500000000000000000000000000000 : ℝ)*base70 + (5978436329549694193/1439500000000000000000000000000000 : ℝ)*base71 + (64430377179169/7197500000000000000000000000 : ℝ)*base74 + (34222002760275305807/1439500000000000000000000000000000 : ℝ)*base76 + (3578105823774194193/1439500000000000000000000000000000 : ℝ)*base77 + (5793865813419305807/1439500000000000000000000000000000 : ℝ)*base80 + (51085915843699/7197500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17346469/5000000000000000000000 : ℝ)*base90 + (17346469/5000000000000000000000 : ℝ)*base92 + (17346469/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2118934020096495813831192519/719750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (589950119/100000000000000 : ℝ)*(base19) + (149314349/25000000000000 : ℝ)*(base23) + (40387501/50000000000000 : ℝ)*(upper3) + (2024279/20000000000000 : ℝ)*(lower4) + (107417773/100000000000000 : ℝ)*(upper5) + (5771695740193787/100000000000000 : ℝ)*(major0) + (5771695740193787/100000000000000 : ℝ)*(major1) + (5771695740193787/100000000000000 : ℝ)*(major2) + (17389562411/100000000000000 : ℝ)*(sp1) + (2024637959/12500000000000 : ℝ)*(sp2) + (1527142184158281/20000000000000 : ℝ)*(sp4) + (3817846470639437/50000000000000 : ℝ)*(sp5) + (7635694126430337/100000000000000 : ℝ)*(sp6) + (976920115365823/25000000000000 : ℝ)*(sp7) + (976920115365823/25000000000000 : ℝ)*(f.failure) + (1527142184158281/20000000000000 : ℝ)*(f.sum) + (1022733584657/224921875000000000000000000 : ℝ)*base66 + (4662566157034485827/1439500000000000000000000000000000 : ℝ)*base68 + (7325605581231485827/1439500000000000000000000000000000 : ℝ)*base70 + (1780022732777485827/1439500000000000000000000000000000 : ℝ)*base72 + (10502199490191/1799375000000000000000000000 : ℝ)*base74 + (10411142991171014173/1439500000000000000000000000000000 : ℝ)*base75 + (16709002014583985827/1439500000000000000000000000000000 : ℝ)*base78 + (3804914398888514173/1439500000000000000000000000000000 : ℝ)*base79 + (39330923096013/14395000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11083829/2500000000000000000000 : ℝ)*base89 + (11083829/2500000000000000000000 : ℝ)*base91 + (11083829/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1051_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_s7_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105584209/5000000000 : ℝ)*x 0 + (5394726609/10000000000 : ℝ)*x 1 + (5264069657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105584209/5000000000 : ℝ)^2061 ≤ (6713760700451/50000000000000 : ℝ)^1549 := by
    have hnat : (1105584209 : ℕ)^2061*50000000000000^1549 ≤ 6713760700451^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105584209 5000000000 6713760700451 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394726609/10000000000 : ℝ)^2061 ≤ (8798441139713/20000000000000 : ℝ)^1549 := by
    have hnat : (5394726609 : ℕ)^2061*20000000000000^1549 ≤ 8798441139713^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394726609 10000000000 8798441139713 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264069657/10000000000 : ℝ)^2061 ≤ (42580272887959/100000000000000 : ℝ)^1549 := by
    have hnat : (5264069657 : ℕ)^2061*100000000000000^1549 ≤ 42580272887959^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264069657 10000000000 42580272887959 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105584209/5000000000 : ℝ), (5394726609/10000000000 : ℝ), (5264069657/10000000000 : ℝ)] ![(6713760700451/50000000000000 : ℝ), (8798441139713/20000000000000 : ℝ), (42580272887959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105584209/5000000000 : ℝ)|^2061 ≤ (6713760700451/50000000000000 : ℝ)^1549
        have hw : |(-1105584209/5000000000 : ℝ)|=(1105584209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394726609/10000000000 : ℝ)|^2061 ≤ (8798441139713/20000000000000 : ℝ)^1549
        have hw : |(5394726609/10000000000 : ℝ)|=(5394726609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264069657/10000000000 : ℝ)|^2061 ≤ (42580272887959/100000000000000 : ℝ)^1549
        have hw : |(5264069657/10000000000 : ℝ)|=(5264069657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345038027/10000000000 : ℝ)*x 0 + (-1138732589/5000000000 : ℝ)*x 1 + (263203489/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345038027/10000000000 : ℝ)^2061 ≤ (21726951526057/50000000000000 : ℝ)^1549 := by
    have hnat : (5345038027 : ℕ)^2061*50000000000000^1549 ≤ 21726951526057^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345038027 10000000000 21726951526057 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138732589/5000000000 : ℝ)^2061 ≤ (3491455681441/25000000000000 : ℝ)^1549 := by
    have hnat : (1138732589 : ℕ)^2061*25000000000000^1549 ≤ 3491455681441^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138732589 5000000000 3491455681441 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263203489/500000000 : ℝ)^2061 ≤ (42580274211747/100000000000000 : ℝ)^1549 := by
    have hnat : (263203489 : ℕ)^2061*100000000000000^1549 ≤ 42580274211747^1549*500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263203489 500000000 42580274211747 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345038027/10000000000 : ℝ), (-1138732589/5000000000 : ℝ), (263203489/500000000 : ℝ)] ![(21726951526057/50000000000000 : ℝ), (3491455681441/25000000000000 : ℝ), (42580274211747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345038027/10000000000 : ℝ)|^2061 ≤ (21726951526057/50000000000000 : ℝ)^1549
        have hw : |(5345038027/10000000000 : ℝ)|=(5345038027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1138732589/5000000000 : ℝ)|^2061 ≤ (3491455681441/25000000000000 : ℝ)^1549
        have hw : |(-1138732589/5000000000 : ℝ)|=(1138732589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263203489/500000000 : ℝ)|^2061 ≤ (42580274211747/100000000000000 : ℝ)^1549
        have hw : |(263203489/500000000 : ℝ)|=(263203489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069007617/2000000000 : ℝ)*x 0 + (1052813941/2000000000 : ℝ)*x 1 + (-5693663/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069007617/2000000000 : ℝ)^2061 ≤ (43453903679497/100000000000000 : ℝ)^1549 := by
    have hnat : (1069007617 : ℕ)^2061*100000000000000^1549 ≤ 43453903679497^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069007617 2000000000 43453903679497 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052813941/2000000000 : ℝ)^2061 ≤ (42580273404559/100000000000000 : ℝ)^1549 := by
    have hnat : (1052813941 : ℕ)^2061*100000000000000^1549 ≤ 42580273404559^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052813941 2000000000 42580273404559 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5693663/25000000 : ℝ)^2061 ≤ (872863931579/6250000000000 : ℝ)^1549 := by
    have hnat : (5693663 : ℕ)^2061*6250000000000^1549 ≤ 872863931579^1549*25000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693663 25000000 872863931579 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069007617/2000000000 : ℝ), (1052813941/2000000000 : ℝ), (-5693663/25000000 : ℝ)] ![(43453903679497/100000000000000 : ℝ), (42580273404559/100000000000000 : ℝ), (872863931579/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069007617/2000000000 : ℝ)|^2061 ≤ (43453903679497/100000000000000 : ℝ)^1549
        have hw : |(1069007617/2000000000 : ℝ)|=(1069007617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052813941/2000000000 : ℝ)|^2061 ≤ (42580273404559/100000000000000 : ℝ)^1549
        have hw : |(1052813941/2000000000 : ℝ)|=(1052813941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5693663/25000000 : ℝ)|^2061 ≤ (872863931579/6250000000000 : ℝ)^1549
        have hw : |(-5693663/25000000 : ℝ)|=(5693663/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (547206067/1250000000 : ℝ)*x 0 + (132871477/312500000 : ℝ)*x 1 + (4507194227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547206067/1250000000 : ℝ)^2061 ≤ (16658203201681/50000000000000 : ℝ)^1549 := by
    have hnat : (547206067 : ℕ)^2061*50000000000000^1549 ≤ 16658203201681^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547206067 1250000000 16658203201681 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132871477/312500000 : ℝ)^2061 ≤ (3204901590239/10000000000000 : ℝ)^1549 := by
    have hnat : (132871477 : ℕ)^2061*10000000000000^1549 ≤ 3204901590239^1549*312500000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132871477 312500000 3204901590239 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507194227/10000000000 : ℝ)^2061 ≤ (17317288837967/50000000000000 : ℝ)^1549 := by
    have hnat : (4507194227 : ℕ)^2061*50000000000000^1549 ≤ 17317288837967^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507194227 10000000000 17317288837967 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547206067/1250000000 : ℝ), (132871477/312500000 : ℝ), (4507194227/10000000000 : ℝ)] ![(16658203201681/50000000000000 : ℝ), (3204901590239/10000000000000 : ℝ), (17317288837967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547206067/1250000000 : ℝ)|^2061 ≤ (16658203201681/50000000000000 : ℝ)^1549
        have hw : |(547206067/1250000000 : ℝ)|=(547206067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132871477/312500000 : ℝ)|^2061 ≤ (3204901590239/10000000000000 : ℝ)^1549
        have hw : |(132871477/312500000 : ℝ)|=(132871477/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507194227/10000000000 : ℝ)|^2061 ≤ (17317288837967/50000000000000 : ℝ)^1549
        have hw : |(4507194227/10000000000 : ℝ)|=(4507194227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-88446939/400000000 : ℝ)*x 0 + (164512417/312500000 : ℝ)*x 1 + (2697198897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88446939/400000000 : ℝ)^2061 ≤ (2685512452093/20000000000000 : ℝ)^1549 := by
    have hnat : (88446939 : ℕ)^2061*20000000000000^1549 ≤ 2685512452093^1549*400000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88446939 400000000 2685512452093 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164512417/312500000 : ℝ)^2061 ≤ (21291899828693/50000000000000 : ℝ)^1549 := by
    have hnat : (164512417 : ℕ)^2061*50000000000000^1549 ≤ 21291899828693^1549*312500000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164512417 312500000 21291899828693 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697198897/5000000000 : ℝ)^2061 ≤ (2199431903301/5000000000000 : ℝ)^1549 := by
    have hnat : (2697198897 : ℕ)^2061*5000000000000^1549 ≤ 2199431903301^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697198897 5000000000 2199431903301 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88446939/400000000 : ℝ), (164512417/312500000 : ℝ), (2697198897/5000000000 : ℝ)] ![(2685512452093/20000000000000 : ℝ), (21291899828693/50000000000000 : ℝ), (2199431903301/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88446939/400000000 : ℝ)|^2061 ≤ (2685512452093/20000000000000 : ℝ)^1549
        have hw : |(-88446939/400000000 : ℝ)|=(88446939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164512417/312500000 : ℝ)|^2061 ≤ (21291899828693/50000000000000 : ℝ)^1549
        have hw : |(164512417/312500000 : ℝ)|=(164512417/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697198897/5000000000 : ℝ)|^2061 ≤ (2199431903301/5000000000000 : ℝ)^1549
        have hw : |(2697198897/5000000000 : ℝ)|=(2697198897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312167687/10000000000 : ℝ)*x 0 + (-2147137131/10000000000 : ℝ)*x 1 + (2697198897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312167687/10000000000 : ℝ)^2061 ≤ (21549354151923/50000000000000 : ℝ)^1549 := by
    have hnat : (5312167687 : ℕ)^2061*50000000000000^1549 ≤ 21549354151923^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312167687 10000000000 21549354151923 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147137131/10000000000 : ℝ)^2061 ≤ (1614081702369/12500000000000 : ℝ)^1549 := by
    have hnat : (2147137131 : ℕ)^2061*12500000000000^1549 ≤ 1614081702369^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147137131 10000000000 1614081702369 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697198897/5000000000 : ℝ)^2061 ≤ (2199431903301/5000000000000 : ℝ)^1549 := by
    have hnat : (2697198897 : ℕ)^2061*5000000000000^1549 ≤ 2199431903301^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697198897 5000000000 2199431903301 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312167687/10000000000 : ℝ), (-2147137131/10000000000 : ℝ), (2697198897/5000000000 : ℝ)] ![(21549354151923/50000000000000 : ℝ), (1614081702369/12500000000000 : ℝ), (2199431903301/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312167687/10000000000 : ℝ)|^2061 ≤ (21549354151923/50000000000000 : ℝ)^1549
        have hw : |(5312167687/10000000000 : ℝ)|=(5312167687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147137131/10000000000 : ℝ)|^2061 ≤ (1614081702369/12500000000000 : ℝ)^1549
        have hw : |(-2147137131/10000000000 : ℝ)|=(2147137131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697198897/5000000000 : ℝ)|^2061 ≤ (2199431903301/5000000000000 : ℝ)^1549
        have hw : |(2697198897/5000000000 : ℝ)|=(2697198897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312167687/10000000000 : ℝ)*x 0 + (2697198897/5000000000 : ℝ)*x 1 + (-2147137131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312167687/10000000000 : ℝ)^2061 ≤ (21549354151923/50000000000000 : ℝ)^1549 := by
    have hnat : (5312167687 : ℕ)^2061*50000000000000^1549 ≤ 21549354151923^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312167687 10000000000 21549354151923 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697198897/5000000000 : ℝ)^2061 ≤ (2199431903301/5000000000000 : ℝ)^1549 := by
    have hnat : (2697198897 : ℕ)^2061*5000000000000^1549 ≤ 2199431903301^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697198897 5000000000 2199431903301 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147137131/10000000000 : ℝ)^2061 ≤ (1614081702369/12500000000000 : ℝ)^1549 := by
    have hnat : (2147137131 : ℕ)^2061*12500000000000^1549 ≤ 1614081702369^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147137131 10000000000 1614081702369 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312167687/10000000000 : ℝ), (2697198897/5000000000 : ℝ), (-2147137131/10000000000 : ℝ)] ![(21549354151923/50000000000000 : ℝ), (2199431903301/5000000000000 : ℝ), (1614081702369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312167687/10000000000 : ℝ)|^2061 ≤ (21549354151923/50000000000000 : ℝ)^1549
        have hw : |(5312167687/10000000000 : ℝ)|=(5312167687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697198897/5000000000 : ℝ)|^2061 ≤ (2199431903301/5000000000000 : ℝ)^1549
        have hw : |(2697198897/5000000000 : ℝ)|=(2697198897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147137131/10000000000 : ℝ)|^2061 ≤ (1614081702369/12500000000000 : ℝ)^1549
        have hw : |(-2147137131/10000000000 : ℝ)|=(2147137131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s7_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4377658487/10000000000 : ℝ)*x 0 + (901310819/2000000000 : ℝ)*x 1 + (265783111/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377658487/10000000000 : ℝ)^2061 ≤ (33316507168597/100000000000000 : ℝ)^1549 := by
    have hnat : (4377658487 : ℕ)^2061*100000000000000^1549 ≤ 33316507168597^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377658487 10000000000 33316507168597 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901310819/2000000000 : ℝ)^2061 ≤ (6925606595799/20000000000000 : ℝ)^1549 := by
    have hnat : (901310819 : ℕ)^2061*20000000000000^1549 ≤ 6925606595799^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901310819 2000000000 6925606595799 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265783111/625000000 : ℝ)^2061 ≤ (8013864961089/25000000000000 : ℝ)^1549 := by
    have hnat : (265783111 : ℕ)^2061*25000000000000^1549 ≤ 8013864961089^1549*625000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265783111 625000000 8013864961089 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377658487/10000000000 : ℝ), (901310819/2000000000 : ℝ), (265783111/625000000 : ℝ)] ![(33316507168597/100000000000000 : ℝ), (6925606595799/20000000000000 : ℝ), (8013864961089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377658487/10000000000 : ℝ)|^2061 ≤ (33316507168597/100000000000000 : ℝ)^1549
        have hw : |(4377658487/10000000000 : ℝ)|=(4377658487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901310819/2000000000 : ℝ)|^2061 ≤ (6925606595799/20000000000000 : ℝ)^1549
        have hw : |(901310819/2000000000 : ℝ)|=(901310819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265783111/625000000 : ℝ)|^2061 ≤ (8013864961089/25000000000000 : ℝ)^1549
        have hw : |(265783111/625000000 : ℝ)|=(265783111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2807/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3499/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5609/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7003/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5609/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7003/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5609/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5609/50000 : ℝ) ^ (8243/2048 : ℝ) ≤ (14996931585939441/100000000000000000000 : ℝ) := by
    have hpowers : (5609/50000 : ℝ)^8243 ≤ (14996931585939441/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5609 : ℕ)^8243*100000000000000000000^2048 ≤ 14996931585939441^2048*50000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5609 50000 14996931585939441 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5609/50000 : ℝ)) (X := (14996931585939441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7003/50000 : ℝ) ^ (8243/2048 : ℝ) ≤ (36643564149484471/100000000000000000000 : ℝ) := by
    have hpowers : (7003/50000 : ℝ)^8243 ≤ (36643564149484471/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7003 : ℕ)^8243*100000000000000000000^2048 ≤ 36643564149484471^2048*50000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7003 50000 36643564149484471 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7003/50000 : ℝ)) (X := (36643564149484471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014996931585939441/50000000000000000000 : ℝ) ≤ (5000372561625419/5000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50014996931585939441/50000000000000000000 : ℝ)^2048 ≤ (5000372561625419/5000000000000000 : ℝ)^8243 := by
      have hnat : (50014996931585939441 : ℕ)^2048*5000000000000000^8243 ≤ 5000372561625419^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014996931585939441 50000000000000000000 5000372561625419 5000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000372561625419/5000000000000000 : ℝ)) (X := (50014996931585939441/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506455061966927989/12500000000000000000 : ℝ) ≤ (2500320693978661/2500000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (12506455061966927989/12500000000000000000 : ℝ)^2048 ≤ (2500320693978661/2500000000000000 : ℝ)^8243 := by
      have hnat : (12506455061966927989 : ℕ)^2048*2500000000000000^8243 ≤ 2500320693978661^8243*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506455061966927989 12500000000000000000 2500320693978661 2500000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500320693978661/2500000000000000 : ℝ)) (X := (12506455061966927989/12500000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036643564149484471/50000000000000000000 : ℝ) ≤ (200036408571569/200000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50036643564149484471/50000000000000000000 : ℝ)^2048 ≤ (200036408571569/200000000000000 : ℝ)^8243 := by
      have hnat : (50036643564149484471 : ℕ)^2048*200000000000000^8243 ≤ 200036408571569^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036643564149484471 50000000000000000000 200036408571569 200000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200036408571569/200000000000000 : ℝ)) (X := (50036643564149484471/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14996931585939441/100000000000000000000 : ℝ) ≤ ((870937957139318279/871250000000000000 : ℝ)+2*(268826331903/139400000000000 : ℝ)*(5609/50000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (870937957139318279/871250000000000000 : ℝ)+2*(268826331903/139400000000000 : ℝ)*(5609/50000 : ℝ)=(5000372561625419/5000000000000000 : ℝ) by norm_num, show 1+2*(14996931585939441/100000000000000000000 : ℝ)=(50014996931585939441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36643564149484471/100000000000000000000 : ℝ)+(14996931585939441/100000000000000000000 : ℝ) ≤ ((870937957139318279/871250000000000000 : ℝ)+(268826331903/139400000000000 : ℝ)*((7003/50000 : ℝ)+(5609/50000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (870937957139318279/871250000000000000 : ℝ)+(268826331903/139400000000000 : ℝ)*((7003/50000 : ℝ)+(5609/50000 : ℝ))=(2500320693978661/2500000000000000 : ℝ) by norm_num, show 1+(36643564149484471/100000000000000000000 : ℝ)+(14996931585939441/100000000000000000000 : ℝ)=(12506455061966927989/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36643564149484471/100000000000000000000 : ℝ) ≤ ((870937957139318279/871250000000000000 : ℝ)+2*(268826331903/139400000000000 : ℝ)*(7003/50000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (870937957139318279/871250000000000000 : ℝ)+2*(268826331903/139400000000000 : ℝ)*(7003/50000 : ℝ)=(200036408571569/200000000000000 : ℝ) by norm_num, show 1+2*(36643564149484471/100000000000000000000 : ℝ)=(50036643564149484471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (870937957139318279/871250000000000000 : ℝ)*(X 1 0+X 2 0)+(268826331903/139400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (870937957139318279/871250000000000000 : ℝ)) (alpha := (268826331903/139400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (870937957139318279/871250000000000000 : ℝ)*(X 0 1+X 2 1)+(268826331903/139400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (870937957139318279/871250000000000000 : ℝ)) (alpha := (268826331903/139400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (870937957139318279/871250000000000000 : ℝ)*(X 0 2+X 1 2)+(268826331903/139400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (5609/50000 : ℝ)) (hi := (7003/50000 : ℝ)) (c := (870937957139318279/871250000000000000 : ℝ)) (alpha := (268826331903/139400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1105584209/5000000000 : ℝ)*X 0 0+(5394726609/10000000000 : ℝ)*X 0 1+(5264069657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345038027/10000000000 : ℝ)*X 1 0+(-1138732589/5000000000 : ℝ)*X 1 1+(263203489/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069007617/2000000000 : ℝ)*X 2 0+(1052813941/2000000000 : ℝ)*X 2 1+(-5693663/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547206067/1250000000 : ℝ)*X 0 0+(132871477/312500000 : ℝ)*X 0 1+(4507194227/10000000000 : ℝ)*X 0 2+(547206067/1250000000 : ℝ)*X 1 0+(132871477/312500000 : ℝ)*X 1 1+(4507194227/10000000000 : ℝ)*X 1 2+(547206067/1250000000 : ℝ)*X 2 0+(132871477/312500000 : ℝ)*X 2 1+(4507194227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-88446939/400000000 : ℝ)*X 0 0+(164512417/312500000 : ℝ)*X 0 1+(2697198897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312167687/10000000000 : ℝ)*X 1 0+(-2147137131/10000000000 : ℝ)*X 1 1+(2697198897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312167687/10000000000 : ℝ)*X 2 0+(2697198897/5000000000 : ℝ)*X 2 1+(-2147137131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377658487/10000000000 : ℝ)*X 0 0+(901310819/2000000000 : ℝ)*X 0 1+(265783111/625000000 : ℝ)*X 0 2+(4377658487/10000000000 : ℝ)*X 1 0+(901310819/2000000000 : ℝ)*X 1 1+(265783111/625000000 : ℝ)*X 1 2+(4377658487/10000000000 : ℝ)*X 2 0+(901310819/2000000000 : ℝ)*X 2 1+(265783111/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194407144543549860086971257/21781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1911261123/100000000000000 : ℝ)*(base19) + (1921596251/100000000000000 : ℝ)*(base23) + (19433773/50000000000000 : ℝ)*(lower2) + (129367583/50000000000000 : ℝ)*(upper3) + (92950673/50000000000000 : ℝ)*(upper5) + (2892663824799113/50000000000000 : ℝ)*(major0) + (2892663824799113/50000000000000 : ℝ)*(major1) + (2892663824799113/50000000000000 : ℝ)*(major2) + (7653688341757693/100000000000000 : ℝ)*(sp0) + (1913435813417473/25000000000000 : ℝ)*(sp1) + (7653743243334763/100000000000000 : ℝ)*(sp2) + (1958440253794687/50000000000000 : ℝ)*(sp3) + (1420579333/2500000000000 : ℝ)*(sp4) + (29329161529/100000000000000 : ℝ)*(sp7) + (489613729593863/12500000000000 : ℝ)*(f.failure) + (3826872582465507/50000000000000 : ℝ)*(f.sum) + (2520845898633/1742500000000000000000000000 : ℝ)*base66 + (479970267314380277/43562500000000000000000000000000 : ℝ)*base67 + (479576040847192777/43562500000000000000000000000000 : ℝ)*base69 + (364885675882442777/43562500000000000000000000000000 : ℝ)*base71 + (3768826899441/871250000000000000000000000 : ℝ)*base73 + (509294971712005277/43562500000000000000000000000000 : ℝ)*base75 + (774614260733255277/43562500000000000000000000000000 : ℝ)*base77 + (333406858614005277/43562500000000000000000000000000 : ℝ)*base79 + (6934136452069/3485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (7219251/1250000000000000000000 : ℝ)*base90 + (7219251/1250000000000000000000 : ℝ)*base92 + (7219251/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85846989391952222081279511/10890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1469874063/100000000000000 : ℝ)*(base19) + (799134927/50000000000000 : ℝ)*(base23) + (158059749/100000000000000 : ℝ)*(upper3) + (29200361/50000000000000 : ℝ)*(lower4) + (20106093/12500000000000 : ℝ)*(upper5) + (1453613799263753/25000000000000 : ℝ)*(major0) + (1453613799263753/25000000000000 : ℝ)*(major1) + (1453613799263753/25000000000000 : ℝ)*(major2) + (19907683593/50000000000000 : ℝ)*(sp1) + (5349788469/12500000000000 : ℝ)*(sp2) + (961534965180827/12500000000000 : ℝ)*(sp4) + (3846119218102683/50000000000000 : ℝ)*(sp5) + (7692235324869009/100000000000000 : ℝ)*(sp6) + (984157602477097/25000000000000 : ℝ)*(sp7) + (984157602477097/25000000000000 : ℝ)*(f.failure) + (961534965180827/12500000000000 : ℝ)*(f.sum) + (2851000626629/1742500000000000000000000000 : ℝ)*base65 + (187083224656090163/21781250000000000000000000000000 : ℝ)*base68 + (266849146240284837/21781250000000000000000000000000 : ℝ)*base69 + (29056828757090163/21781250000000000000000000000000 : ℝ)*base72 + (807696917187/217812500000000000000000000 : ℝ)*base74 + (274071011982159837/21781250000000000000000000000000 : ℝ)*base75 + (46679093675308913/21781250000000000000000000000000 : ℝ)*base78 + (33530452380902663/21781250000000000000000000000000 : ℝ)*base80 + (17188982405053/3485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4099331/2500000000000000000000 : ℝ)*base89 + (4099331/2500000000000000000000 : ℝ)*base91 + (4099331/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1051_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5609/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_s8_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211176231/10000000000 : ℝ)*x 0 + (2697309507/5000000000 : ℝ)*x 1 + (5264172261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211176231/10000000000 : ℝ)^2061 ≤ (2685516905683/20000000000000 : ℝ)^1549 := by
    have hnat : (2211176231 : ℕ)^2061*20000000000000^1549 ≤ 2685516905683^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211176231 10000000000 2685516905683 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697309507/5000000000 : ℝ)^2061 ≤ (21995519144121/50000000000000 : ℝ)^1549 := by
    have hnat : (2697309507 : ℕ)^2061*50000000000000^1549 ≤ 21995519144121^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697309507 5000000000 21995519144121 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264172261/10000000000 : ℝ)^2061 ≤ (2661336072977/6250000000000 : ℝ)^1549 := by
    have hnat : (5264172261 : ℕ)^2061*6250000000000^1549 ≤ 2661336072977^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264172261 10000000000 2661336072977 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211176231/10000000000 : ℝ), (2697309507/5000000000 : ℝ), (5264172261/10000000000 : ℝ)] ![(2685516905683/20000000000000 : ℝ), (21995519144121/50000000000000 : ℝ), (2661336072977/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211176231/10000000000 : ℝ)|^2061 ≤ (2685516905683/20000000000000 : ℝ)^1549
        have hw : |(-2211176231/10000000000 : ℝ)|=(2211176231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697309507/5000000000 : ℝ)|^2061 ≤ (21995519144121/50000000000000 : ℝ)^1549
        have hw : |(2697309507/5000000000 : ℝ)|=(2697309507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264172261/10000000000 : ℝ)|^2061 ≤ (2661336072977/6250000000000 : ℝ)^1549
        have hw : |(5264172261/10000000000 : ℝ)|=(5264172261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345011683/10000000000 : ℝ)*x 0 + (-284670617/1250000000 : ℝ)*x 1 + (21056689/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345011683/10000000000 : ℝ)^2061 ≤ (1357925565337/3125000000000 : ℝ)^1549 := by
    have hnat : (5345011683 : ℕ)^2061*3125000000000^1549 ≤ 1357925565337^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345011683 10000000000 1357925565337 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284670617/1250000000 : ℝ)^2061 ≤ (13965004848911/100000000000000 : ℝ)^1549 := by
    have hnat : (284670617 : ℕ)^2061*100000000000000^1549 ≤ 13965004848911^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284670617 1250000000 13965004848911 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21056689/40000000 : ℝ)^2061 ≤ (10645344262311/25000000000000 : ℝ)^1549 := by
    have hnat : (21056689 : ℕ)^2061*25000000000000^1549 ≤ 10645344262311^1549*40000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21056689 40000000 10645344262311 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345011683/10000000000 : ℝ), (-284670617/1250000000 : ℝ), (21056689/40000000 : ℝ)] ![(1357925565337/3125000000000 : ℝ), (13965004848911/100000000000000 : ℝ), (10645344262311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345011683/10000000000 : ℝ)|^2061 ≤ (1357925565337/3125000000000 : ℝ)^1549
        have hw : |(5345011683/10000000000 : ℝ)|=(5345011683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284670617/1250000000 : ℝ)|^2061 ≤ (13965004848911/100000000000000 : ℝ)^1549
        have hw : |(-284670617/1250000000 : ℝ)|=(284670617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21056689/40000000 : ℝ)|^2061 ≤ (10645344262311/25000000000000 : ℝ)^1549
        have hw : |(21056689/40000000 : ℝ)|=(21056689/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345011743/10000000000 : ℝ)*x 0 + (1316043039/2500000000 : ℝ)*x 1 + (-2277364981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345011743/10000000000 : ℝ)^2061 ≤ (43453618739799/100000000000000 : ℝ)^1549 := by
    have hnat : (5345011743 : ℕ)^2061*100000000000000^1549 ≤ 43453618739799^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345011743 10000000000 43453618739799 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316043039/2500000000 : ℝ)^2061 ≤ (21290688018781/50000000000000 : ℝ)^1549 := by
    have hnat : (1316043039 : ℕ)^2061*50000000000000^1549 ≤ 21290688018781^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316043039 2500000000 21290688018781 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277364981/10000000000 : ℝ)^2061 ≤ (218203206501/1562500000000 : ℝ)^1549 := by
    have hnat : (2277364981 : ℕ)^2061*1562500000000^1549 ≤ 218203206501^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277364981 10000000000 218203206501 1562500000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345011743/10000000000 : ℝ), (1316043039/2500000000 : ℝ), (-2277364981/10000000000 : ℝ)] ![(43453618739799/100000000000000 : ℝ), (21290688018781/50000000000000 : ℝ), (218203206501/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345011743/10000000000 : ℝ)|^2061 ≤ (43453618739799/100000000000000 : ℝ)^1549
        have hw : |(5345011743/10000000000 : ℝ)|=(5345011743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316043039/2500000000 : ℝ)|^2061 ≤ (21290688018781/50000000000000 : ℝ)^1549
        have hw : |(1316043039/2500000000 : ℝ)|=(1316043039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2277364981/10000000000 : ℝ)|^2061 ≤ (218203206501/1562500000000 : ℝ)^1549
        have hw : |(-2277364981/10000000000 : ℝ)|=(2277364981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4377653851/10000000000 : ℝ)*x 0 + (425209179/1000000000 : ℝ)*x 1 + (2253494169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377653851/10000000000 : ℝ)^2061 ≤ (6663292044759/20000000000000 : ℝ)^1549 := by
    have hnat : (4377653851 : ℕ)^2061*20000000000000^1549 ≤ 6663292044759^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377653851 10000000000 6663292044759 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425209179/1000000000 : ℝ)^2061 ≤ (16025533559463/50000000000000 : ℝ)^1549 := by
    have hnat : (425209179 : ℕ)^2061*50000000000000^1549 ≤ 16025533559463^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425209179 1000000000 16025533559463 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253494169/5000000000 : ℝ)^2061 ≤ (1731623631867/5000000000000 : ℝ)^1549 := by
    have hnat : (2253494169 : ℕ)^2061*5000000000000^1549 ≤ 1731623631867^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253494169 5000000000 1731623631867 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377653851/10000000000 : ℝ), (425209179/1000000000 : ℝ), (2253494169/5000000000 : ℝ)] ![(6663292044759/20000000000000 : ℝ), (16025533559463/50000000000000 : ℝ), (1731623631867/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377653851/10000000000 : ℝ)|^2061 ≤ (6663292044759/20000000000000 : ℝ)^1549
        have hw : |(4377653851/10000000000 : ℝ)|=(4377653851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425209179/1000000000 : ℝ)|^2061 ≤ (16025533559463/50000000000000 : ℝ)^1549
        have hw : |(425209179/1000000000 : ℝ)|=(425209179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253494169/5000000000 : ℝ)|^2061 ≤ (1731623631867/5000000000000 : ℝ)^1549
        have hw : |(2253494169/5000000000 : ℝ)|=(2253494169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211181333/10000000000 : ℝ)*x 0 + (5264498793/10000000000 : ℝ)*x 1 + (5394291307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211181333/10000000000 : ℝ)^2061 ≤ (6713812875809/50000000000000 : ℝ)^1549 := by
    have hnat : (2211181333 : ℕ)^2061*50000000000000^1549 ≤ 6713812875809^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211181333 10000000000 6713812875809 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264498793/10000000000 : ℝ)^2061 ≤ (34067913223/80000000000 : ℝ)^1549 := by
    have hnat : (5264498793 : ℕ)^2061*80000000000^1549 ≤ 34067913223^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264498793 10000000000 34067913223 80000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394291307/10000000000 : ℝ)^2061 ≤ (43987482700783/100000000000000 : ℝ)^1549 := by
    have hnat : (5394291307 : ℕ)^2061*100000000000000^1549 ≤ 43987482700783^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394291307 10000000000 43987482700783 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211181333/10000000000 : ℝ), (5264498793/10000000000 : ℝ), (5394291307/10000000000 : ℝ)] ![(6713812875809/50000000000000 : ℝ), (34067913223/80000000000 : ℝ), (43987482700783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211181333/10000000000 : ℝ)|^2061 ≤ (6713812875809/50000000000000 : ℝ)^1549
        have hw : |(-2211181333/10000000000 : ℝ)|=(2211181333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264498793/10000000000 : ℝ)|^2061 ≤ (34067913223/80000000000 : ℝ)^1549
        have hw : |(5264498793/10000000000 : ℝ)|=(5264498793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394291307/10000000000 : ℝ)|^2061 ≤ (43987482700783/100000000000000 : ℝ)^1549
        have hw : |(5394291307/10000000000 : ℝ)|=(5394291307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062438823/2000000000 : ℝ)*x 0 + (-429449171/2000000000 : ℝ)*x 1 + (1348572829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062438823/2000000000 : ℝ)^2061 ≤ (43098993591979/100000000000000 : ℝ)^1549 := by
    have hnat : (1062438823 : ℕ)^2061*100000000000000^1549 ≤ 43098993591979^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062438823 2000000000 43098993591979 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429449171/2000000000 : ℝ)^2061 ≤ (12913523603119/100000000000000 : ℝ)^1549 := by
    have hnat : (429449171 : ℕ)^2061*100000000000000^1549 ≤ 12913523603119^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429449171 2000000000 12913523603119 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348572829/2500000000 : ℝ)^2061 ≤ (43987482798431/100000000000000 : ℝ)^1549 := by
    have hnat : (1348572829 : ℕ)^2061*100000000000000^1549 ≤ 43987482798431^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348572829 2500000000 43987482798431 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062438823/2000000000 : ℝ), (-429449171/2000000000 : ℝ), (1348572829/2500000000 : ℝ)] ![(43098993591979/100000000000000 : ℝ), (12913523603119/100000000000000 : ℝ), (43987482798431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062438823/2000000000 : ℝ)|^2061 ≤ (43098993591979/100000000000000 : ℝ)^1549
        have hw : |(1062438823/2000000000 : ℝ)|=(1062438823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429449171/2000000000 : ℝ)|^2061 ≤ (12913523603119/100000000000000 : ℝ)^1549
        have hw : |(-429449171/2000000000 : ℝ)|=(429449171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348572829/2500000000 : ℝ)|^2061 ≤ (43987482798431/100000000000000 : ℝ)^1549
        have hw : |(1348572829/2500000000 : ℝ)|=(1348572829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664024263/1250000000 : ℝ)*x 0 + (2697145657/5000000000 : ℝ)*x 1 + (-134202867/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664024263/1250000000 : ℝ)^2061 ≤ (8619798694647/20000000000000 : ℝ)^1549 := by
    have hnat : (664024263 : ℕ)^2061*20000000000000^1549 ≤ 8619798694647^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664024263 1250000000 8619798694647 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697145657/5000000000 : ℝ)^2061 ≤ (10996870694183/25000000000000 : ℝ)^1549 := by
    have hnat : (2697145657 : ℕ)^2061*25000000000000^1549 ≤ 10996870694183^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697145657 5000000000 10996870694183 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134202867/625000000 : ℝ)^2061 ≤ (12913523739151/100000000000000 : ℝ)^1549 := by
    have hnat : (134202867 : ℕ)^2061*100000000000000^1549 ≤ 12913523739151^1549*625000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134202867 625000000 12913523739151 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664024263/1250000000 : ℝ), (2697145657/5000000000 : ℝ), (-134202867/625000000 : ℝ)] ![(8619798694647/20000000000000 : ℝ), (10996870694183/25000000000000 : ℝ), (12913523739151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664024263/1250000000 : ℝ)|^2061 ≤ (8619798694647/20000000000000 : ℝ)^1549
        have hw : |(664024263/1250000000 : ℝ)|=(664024263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697145657/5000000000 : ℝ)|^2061 ≤ (10996870694183/25000000000000 : ℝ)^1549
        have hw : |(2697145657/5000000000 : ℝ)|=(2697145657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134202867/625000000 : ℝ)|^2061 ≤ (12913523739151/100000000000000 : ℝ)^1549
        have hw : |(-134202867/625000000 : ℝ)|=(134202867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s8_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (437766381/1000000000 : ℝ)*x 0 + (901270043/2000000000 : ℝ)*x 1 + (170109289/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437766381/1000000000 : ℝ)^2061 ≤ (3253570417/9765625000 : ℝ)^1549 := by
    have hnat : (437766381 : ℕ)^2061*9765625000^1549 ≤ 3253570417^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437766381 1000000000 3253570417 9765625000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901270043/2000000000 : ℝ)^2061 ≤ (17312974289207/50000000000000 : ℝ)^1549 := by
    have hnat : (901270043 : ℕ)^2061*50000000000000^1549 ≤ 17312974289207^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901270043 2000000000 17312974289207 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170109289/400000000 : ℝ)^2061 ≤ (8014372582911/25000000000000 : ℝ)^1549 := by
    have hnat : (170109289 : ℕ)^2061*25000000000000^1549 ≤ 8014372582911^1549*400000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170109289 400000000 8014372582911 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437766381/1000000000 : ℝ), (901270043/2000000000 : ℝ), (170109289/400000000 : ℝ)] ![(3253570417/9765625000 : ℝ), (17312974289207/50000000000000 : ℝ), (8014372582911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437766381/1000000000 : ℝ)|^2061 ≤ (3253570417/9765625000 : ℝ)^1549
        have hw : |(437766381/1000000000 : ℝ)|=(437766381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901270043/2000000000 : ℝ)|^2061 ≤ (17312974289207/50000000000000 : ℝ)^1549
        have hw : |(901270043/2000000000 : ℝ)|=(901270043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170109289/400000000 : ℝ)|^2061 ≤ (8014372582911/25000000000000 : ℝ)^1549
        have hw : |(170109289/400000000 : ℝ)|=(170109289/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6997/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2807/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2807/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2807/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2807/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2807/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2807/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2807/25000 : ℝ) ^ (8243/2048 : ℝ) ≤ (7525405806871613/50000000000000000000 : ℝ) := by
    have hpowers : (2807/25000 : ℝ)^8243 ≤ (7525405806871613/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2807 : ℕ)^8243*50000000000000000000^2048 ≤ 7525405806871613^2048*25000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 25000 7525405806871613 50000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/25000 : ℝ)) (X := (7525405806871613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3499/25000 : ℝ) ^ (8243/2048 : ℝ) ≤ (36538375245454521/100000000000000000000 : ℝ) := by
    have hpowers : (3499/25000 : ℝ)^8243 ≤ (36538375245454521/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3499 : ℕ)^8243*100000000000000000000^2048 ≤ 36538375245454521^2048*25000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3499 25000 36538375245454521 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3499/25000 : ℝ)) (X := (36538375245454521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007525405806871613/25000000000000000000 : ℝ) ≤ (2000149559995963/2000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (25007525405806871613/25000000000000000000 : ℝ)^2048 ≤ (2000149559995963/2000000000000000 : ℝ)^8243 := by
      have hnat : (25007525405806871613 : ℕ)^2048*2000000000000000^8243 ≤ 2000149559995963^8243*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007525405806871613 25000000000000000000 2000149559995963 2000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000149559995963/2000000000000000 : ℝ)) (X := (25007525405806871613/25000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051589186859197747/100000000000000000000 : ℝ) ≤ (1250160187702913/1250000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (100051589186859197747/100000000000000000000 : ℝ)^2048 ≤ (1250160187702913/1250000000000000 : ℝ)^8243 := by
      have hnat : (100051589186859197747 : ℕ)^2048*1250000000000000^8243 ≤ 1250160187702913^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051589186859197747 100000000000000000000 1250160187702913 1250000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250160187702913/1250000000000000 : ℝ)) (X := (100051589186859197747/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036538375245454521/50000000000000000000 : ℝ) ≤ (10001815203266793/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50036538375245454521/50000000000000000000 : ℝ)^2048 ≤ (10001815203266793/10000000000000000 : ℝ)^8243 := by
      have hnat : (50036538375245454521 : ℕ)^2048*10000000000000000^8243 ≤ 10001815203266793^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036538375245454521 50000000000000000000 10001815203266793 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001815203266793/10000000000000000 : ℝ)) (X := (50036538375245454521/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7525405806871613/50000000000000000000 : ℝ) ≤ ((3458760638279742367/3460000000000000000 : ℝ)+2*(533701643489/276800000000000 : ℝ)*(2807/25000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (3458760638279742367/3460000000000000000 : ℝ)+2*(533701643489/276800000000000 : ℝ)*(2807/25000 : ℝ)=(2000149559995963/2000000000000000 : ℝ) by norm_num, show 1+2*(7525405806871613/50000000000000000000 : ℝ)=(25007525405806871613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36538375245454521/100000000000000000000 : ℝ)+(7525405806871613/50000000000000000000 : ℝ) ≤ ((3458760638279742367/3460000000000000000 : ℝ)+(533701643489/276800000000000 : ℝ)*((3499/25000 : ℝ)+(2807/25000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (3458760638279742367/3460000000000000000 : ℝ)+(533701643489/276800000000000 : ℝ)*((3499/25000 : ℝ)+(2807/25000 : ℝ))=(1250160187702913/1250000000000000 : ℝ) by norm_num, show 1+(36538375245454521/100000000000000000000 : ℝ)+(7525405806871613/50000000000000000000 : ℝ)=(100051589186859197747/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36538375245454521/100000000000000000000 : ℝ) ≤ ((3458760638279742367/3460000000000000000 : ℝ)+2*(533701643489/276800000000000 : ℝ)*(3499/25000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (3458760638279742367/3460000000000000000 : ℝ)+2*(533701643489/276800000000000 : ℝ)*(3499/25000 : ℝ)=(10001815203266793/10000000000000000 : ℝ) by norm_num, show 1+2*(36538375245454521/100000000000000000000 : ℝ)=(50036538375245454521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3458760638279742367/3460000000000000000 : ℝ)*(X 1 0+X 2 0)+(533701643489/276800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (2807/25000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (3458760638279742367/3460000000000000000 : ℝ)) (alpha := (533701643489/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3458760638279742367/3460000000000000000 : ℝ)*(X 0 1+X 2 1)+(533701643489/276800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (2807/25000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (3458760638279742367/3460000000000000000 : ℝ)) (alpha := (533701643489/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3458760638279742367/3460000000000000000 : ℝ)*(X 0 2+X 1 2)+(533701643489/276800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (2807/25000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (3458760638279742367/3460000000000000000 : ℝ)) (alpha := (533701643489/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2211176231/10000000000 : ℝ)*X 0 0+(2697309507/5000000000 : ℝ)*X 0 1+(5264172261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345011683/10000000000 : ℝ)*X 1 0+(-284670617/1250000000 : ℝ)*X 1 1+(21056689/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345011743/10000000000 : ℝ)*X 2 0+(1316043039/2500000000 : ℝ)*X 2 1+(-2277364981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377653851/10000000000 : ℝ)*X 0 0+(425209179/1000000000 : ℝ)*X 0 1+(2253494169/5000000000 : ℝ)*X 0 2+(4377653851/10000000000 : ℝ)*X 1 0+(425209179/1000000000 : ℝ)*X 1 1+(2253494169/5000000000 : ℝ)*X 1 2+(4377653851/10000000000 : ℝ)*X 2 0+(425209179/1000000000 : ℝ)*X 2 1+(2253494169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2211181333/10000000000 : ℝ)*X 0 0+(5264498793/10000000000 : ℝ)*X 0 1+(5394291307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062438823/2000000000 : ℝ)*X 1 0+(-429449171/2000000000 : ℝ)*X 1 1+(1348572829/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664024263/1250000000 : ℝ)*X 2 0+(2697145657/5000000000 : ℝ)*X 2 1+(-134202867/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437766381/1000000000 : ℝ)*X 0 0+(901270043/2000000000 : ℝ)*X 0 1+(170109289/400000000 : ℝ)*X 0 2+(437766381/1000000000 : ℝ)*X 1 0+(901270043/2000000000 : ℝ)*X 1 1+(170109289/400000000 : ℝ)*X 1 2+(437766381/1000000000 : ℝ)*X 2 0+(901270043/2000000000 : ℝ)*X 2 1+(170109289/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11603742095774441694532197/6920000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185680227/50000000000000 : ℝ)*(base19) + (107256833/25000000000000 : ℝ)*(base23) + (4590859/25000000000000 : ℝ)*(lower2) + (74892573/100000000000000 : ℝ)*(upper3) + (127623/4000000000000 : ℝ)*(lower4) + (231783011344499/4000000000000 : ℝ)*(major0) + (231783011344499/4000000000000 : ℝ)*(major1) + (231783011344499/4000000000000 : ℝ)*(major2) + (7665972525581479/100000000000000 : ℝ)*(sp0) + (7665979266535909/100000000000000 : ℝ)*(sp1) + (7665979208869031/100000000000000 : ℝ)*(sp2) + (392316448593187/10000000000000 : ℝ)*(sp3) + (1778078721/25000000000000 : ℝ)*(sp4) + (1596875499/25000000000000 : ℝ)*(sp7) + (1961585436716933/50000000000000 : ℝ)*(f.failure) + (7665979637896363/100000000000000 : ℝ)*(f.sum) + (2316663803343/2768000000000000000000000000 : ℝ)*base65 + (42618650241393367/13840000000000000000000000000000 : ℝ)*base68 + (229474807181953367/13840000000000000000000000000000 : ℝ)*base70 + (122996772856353367/13840000000000000000000000000000 : ℝ)*base72 + (3465077872033/2768000000000000000000000000 : ℝ)*base74 + (364155415729073367/13840000000000000000000000000000 : ℝ)*base76 + (204652858470593367/13840000000000000000000000000000 : ℝ)*base78 + (194406416034513367/13840000000000000000000000000000 : ℝ)*base80 + (10125882720177/2768000000000000000000000000 : ℝ)*base82 + (30602359/5000000000000000000000 : ℝ)*base89 + (30602359/5000000000000000000000 : ℝ)*base91 + (30602359/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (888570090734103908162399073/86500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (962224391/50000000000000 : ℝ)*(base19) + (1038787859/50000000000000 : ℝ)*(base23) + (202560717/100000000000000 : ℝ)*(upper3) + (8083511/10000000000000 : ℝ)*(lower4) + (212388367/100000000000000 : ℝ)*(upper5) + (2911885018350773/50000000000000 : ℝ)*(major0) + (2911885018350773/50000000000000 : ℝ)*(major1) + (2911885018350773/50000000000000 : ℝ)*(major2) + (26541785591/50000000000000 : ℝ)*(sp1) + (55820993697/100000000000000 : ℝ)*(sp2) + (7704602783359427/100000000000000 : ℝ)*(sp4) + (963068471917433/12500000000000 : ℝ)*(sp5) + (1926136221197503/25000000000000 : ℝ)*(sp6) + (49286711845343/1250000000000 : ℝ)*(sp7) + (49286711845343/1250000000000 : ℝ)*(f.failure) + (7704602783359427/100000000000000 : ℝ)*(f.sum) + (10516719720717/6920000000000000000000000000 : ℝ)*base65 + (292076842240237809/173000000000000000000000000000000 : ℝ)*base68 + (856248046865762191/173000000000000000000000000000000 : ℝ)*base69 + (809995394155237809/173000000000000000000000000000000 : ℝ)*base72 + (15129722846763/6920000000000000000000000000 : ℝ)*base74 + (3549853148189237809/173000000000000000000000000000000 : ℝ)*base76 + (664258800475762191/173000000000000000000000000000000 : ℝ)*base77 + (35653628037237809/173000000000000000000000000000000 : ℝ)*base80 + (4150814016317/6920000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11211/125000000000000000000 : ℝ)*base90 + (11211/125000000000000000000 : ℝ)*base92 + (11211/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1051_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1051_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1051_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1051_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1051_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
