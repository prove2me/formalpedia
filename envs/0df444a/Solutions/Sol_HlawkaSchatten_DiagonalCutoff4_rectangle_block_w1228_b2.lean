-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:04.053614+00:00
-- url     : https://prove2.me/submissions/404faaf6-e0e9-416c-8924-b468fe0e2a5f

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
theorem support_rectangle_w1228_s6_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126409023/10000000000 : ℝ)*x 0 + (1347916981/2500000000 : ℝ)*x 1 + (2633412637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126409023/10000000000 : ℝ)^8421 ≤ (3232378957503/25000000000000 : ℝ)^6373 := by
    have hnat : (2126409023 : ℕ)^8421*25000000000000^6373 ≤ 3232378957503^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126409023 10000000000 3232378957503 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347916981/2500000000 : ℝ)^8421 ≤ (11052253559647/25000000000000 : ℝ)^6373 := by
    have hnat : (1347916981 : ℕ)^8421*25000000000000^6373 ≤ 11052253559647^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347916981 2500000000 11052253559647 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633412637/5000000000 : ℝ)^8421 ≤ (10715367478923/25000000000000 : ℝ)^6373 := by
    have hnat : (2633412637 : ℕ)^8421*25000000000000^6373 ≤ 10715367478923^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633412637 5000000000 10715367478923 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126409023/10000000000 : ℝ), (1347916981/2500000000 : ℝ), (2633412637/5000000000 : ℝ)] ![(3232378957503/25000000000000 : ℝ), (11052253559647/25000000000000 : ℝ), (10715367478923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126409023/10000000000 : ℝ)|^8421 ≤ (3232378957503/25000000000000 : ℝ)^6373
        have hw : |(-2126409023/10000000000 : ℝ)|=(2126409023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347916981/2500000000 : ℝ)|^8421 ≤ (11052253559647/25000000000000 : ℝ)^6373
        have hw : |(1347916981/2500000000 : ℝ)|=(1347916981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633412637/5000000000 : ℝ)|^8421 ≤ (10715367478923/25000000000000 : ℝ)^6373
        have hw : |(2633412637/5000000000 : ℝ)|=(2633412637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213777359/400000000 : ℝ)*x 0 + (-437942729/2000000000 : ℝ)*x 1 + (1053365041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213777359/400000000 : ℝ)^8421 ≤ (4369798149451/10000000000000 : ℝ)^6373 := by
    have hnat : (213777359 : ℕ)^8421*10000000000000^6373 ≤ 4369798149451^6373*400000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213777359 400000000 4369798149451 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437942729/2000000000 : ℝ)^8421 ≤ (840034332411/6250000000000 : ℝ)^6373 := by
    have hnat : (437942729 : ℕ)^8421*6250000000000^6373 ≤ 840034332411^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437942729 2000000000 840034332411 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053365041/2000000000 : ℝ)^8421 ≤ (42861469173721/100000000000000 : ℝ)^6373 := by
    have hnat : (1053365041 : ℕ)^8421*100000000000000^6373 ≤ 42861469173721^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053365041 2000000000 42861469173721 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213777359/400000000 : ℝ), (-437942729/2000000000 : ℝ), (1053365041/2000000000 : ℝ)] ![(4369798149451/10000000000000 : ℝ), (840034332411/6250000000000 : ℝ), (42861469173721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213777359/400000000 : ℝ)|^8421 ≤ (4369798149451/10000000000000 : ℝ)^6373
        have hw : |(213777359/400000000 : ℝ)|=(213777359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437942729/2000000000 : ℝ)|^8421 ≤ (840034332411/6250000000000 : ℝ)^6373
        have hw : |(-437942729/2000000000 : ℝ)|=(437942729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053365041/2000000000 : ℝ)|^8421 ≤ (42861469173721/100000000000000 : ℝ)^6373
        have hw : |(1053365041/2000000000 : ℝ)|=(1053365041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344433941/10000000000 : ℝ)*x 0 + (2633412617/5000000000 : ℝ)*x 1 + (-547428413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344433941/10000000000 : ℝ)^8421 ≤ (21848990563589/50000000000000 : ℝ)^6373 := by
    have hnat : (5344433941 : ℕ)^8421*50000000000000^6373 ≤ 21848990563589^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344433941 10000000000 21848990563589 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633412617/5000000000 : ℝ)^8421 ≤ (10715367371391/25000000000000 : ℝ)^6373 := by
    have hnat : (2633412617 : ℕ)^8421*25000000000000^6373 ≤ 10715367371391^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633412617 5000000000 10715367371391 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547428413/2500000000 : ℝ)^8421 ≤ (268810987507/2000000000000 : ℝ)^6373 := by
    have hnat : (547428413 : ℕ)^8421*2000000000000^6373 ≤ 268810987507^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547428413 2500000000 268810987507 2000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344433941/10000000000 : ℝ), (2633412617/5000000000 : ℝ), (-547428413/2500000000 : ℝ)] ![(21848990563589/50000000000000 : ℝ), (10715367371391/25000000000000 : ℝ), (268810987507/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344433941/10000000000 : ℝ)|^8421 ≤ (21848990563589/50000000000000 : ℝ)^6373
        have hw : |(5344433941/10000000000 : ℝ)|=(5344433941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633412617/5000000000 : ℝ)|^8421 ≤ (10715367371391/25000000000000 : ℝ)^6373
        have hw : |(2633412617/5000000000 : ℝ)|=(2633412617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547428413/2500000000 : ℝ)|^8421 ≤ (268810987507/2000000000000 : ℝ)^6373
        have hw : |(-547428413/2500000000 : ℝ)|=(547428413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088171593/2500000000 : ℝ)*x 0 + (132130919/312500000 : ℝ)*x 1 + (2240378611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088171593/2500000000 : ℝ)^8421 ≤ (33317314795817/100000000000000 : ℝ)^6373 := by
    have hnat : (1088171593 : ℕ)^8421*100000000000000^6373 ≤ 33317314795817^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088171593 2500000000 33317314795817 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132130919/312500000 : ℝ)^8421 ≤ (8015987508717/25000000000000 : ℝ)^6373 := by
    have hnat : (132130919 : ℕ)^8421*25000000000000^6373 ≤ 8015987508717^6373*312500000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132130919 312500000 8015987508717 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240378611/5000000000 : ℝ)^8421 ≤ (17309367570669/50000000000000 : ℝ)^6373 := by
    have hnat : (2240378611 : ℕ)^8421*50000000000000^6373 ≤ 17309367570669^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240378611 5000000000 17309367570669 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088171593/2500000000 : ℝ), (132130919/312500000 : ℝ), (2240378611/5000000000 : ℝ)] ![(33317314795817/100000000000000 : ℝ), (8015987508717/25000000000000 : ℝ), (17309367570669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088171593/2500000000 : ℝ)|^8421 ≤ (33317314795817/100000000000000 : ℝ)^6373
        have hw : |(1088171593/2500000000 : ℝ)|=(1088171593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132130919/312500000 : ℝ)|^8421 ≤ (8015987508717/25000000000000 : ℝ)^6373
        have hw : |(132130919/312500000 : ℝ)|=(132130919/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240378611/5000000000 : ℝ)|^8421 ≤ (17309367570669/50000000000000 : ℝ)^6373
        have hw : |(2240378611/5000000000 : ℝ)|=(2240378611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-531603449/2500000000 : ℝ)*x 0 + (658392609/1250000000 : ℝ)*x 1 + (1347837787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531603449/2500000000 : ℝ)^8421 ≤ (3232388544593/25000000000000 : ℝ)^6373 := by
    have hnat : (531603449 : ℕ)^8421*25000000000000^6373 ≤ 3232388544593^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531603449 2500000000 3232388544593 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658392609/1250000000 : ℝ)^8421 ≤ (42864863638151/100000000000000 : ℝ)^6373 := by
    have hnat : (658392609 : ℕ)^8421*100000000000000^6373 ≤ 42864863638151^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658392609 1250000000 42864863638151 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347837787/2500000000 : ℝ)^8421 ≤ (8841116434543/20000000000000 : ℝ)^6373 := by
    have hnat : (1347837787 : ℕ)^8421*20000000000000^6373 ≤ 8841116434543^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347837787 2500000000 8841116434543 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531603449/2500000000 : ℝ), (658392609/1250000000 : ℝ), (1347837787/2500000000 : ℝ)] ![(3232388544593/25000000000000 : ℝ), (42864863638151/100000000000000 : ℝ), (8841116434543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531603449/2500000000 : ℝ)|^8421 ≤ (3232388544593/25000000000000 : ℝ)^6373
        have hw : |(-531603449/2500000000 : ℝ)|=(531603449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658392609/1250000000 : ℝ)|^8421 ≤ (42864863638151/100000000000000 : ℝ)^6373
        have hw : |(658392609/1250000000 : ℝ)|=(658392609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347837787/2500000000 : ℝ)|^8421 ≤ (8841116434543/20000000000000 : ℝ)^6373
        have hw : |(1347837787/2500000000 : ℝ)|=(1347837787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312610197/10000000000 : ℝ)*x 0 + (-413037577/2000000000 : ℝ)*x 1 + (269567547/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312610197/10000000000 : ℝ)^8421 ≤ (21677245443443/50000000000000 : ℝ)^6373 := by
    have hnat : (5312610197 : ℕ)^8421*50000000000000^6373 ≤ 21677245443443^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312610197 10000000000 21677245443443 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413037577/2000000000 : ℝ)^8421 ≤ (12439929182573/100000000000000 : ℝ)^6373 := by
    have hnat : (413037577 : ℕ)^8421*100000000000000^6373 ≤ 12439929182573^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413037577 2000000000 12439929182573 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269567547/500000000 : ℝ)^8421 ≤ (44205579919189/100000000000000 : ℝ)^6373 := by
    have hnat : (269567547 : ℕ)^8421*100000000000000^6373 ≤ 44205579919189^6373*500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269567547 500000000 44205579919189 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312610197/10000000000 : ℝ), (-413037577/2000000000 : ℝ), (269567547/500000000 : ℝ)] ![(21677245443443/50000000000000 : ℝ), (12439929182573/100000000000000 : ℝ), (44205579919189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312610197/10000000000 : ℝ)|^8421 ≤ (21677245443443/50000000000000 : ℝ)^6373
        have hw : |(5312610197/10000000000 : ℝ)|=(5312610197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413037577/2000000000 : ℝ)|^8421 ≤ (12439929182573/100000000000000 : ℝ)^6373
        have hw : |(-413037577/2000000000 : ℝ)|=(413037577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269567547/500000000 : ℝ)|^8421 ≤ (44205579919189/100000000000000 : ℝ)^6373
        have hw : |(269567547/500000000 : ℝ)|=(269567547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312610157/10000000000 : ℝ)*x 0 + (1078270219/2000000000 : ℝ)*x 1 + (-2065187727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312610157/10000000000 : ℝ)^8421 ≤ (1083862261389/2500000000000 : ℝ)^6373 := by
    have hnat : (5312610157 : ℕ)^8421*2500000000000^6373 ≤ 1083862261389^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312610157 10000000000 1083862261389 2500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078270219/2000000000 : ℝ)^8421 ≤ (44205581598499/100000000000000 : ℝ)^6373 := by
    have hnat : (1078270219 : ℕ)^8421*100000000000000^6373 ≤ 44205581598499^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078270219 2000000000 44205581598499 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065187727/10000000000 : ℝ)^8421 ≤ (6219963962497/50000000000000 : ℝ)^6373 := by
    have hnat : (2065187727 : ℕ)^8421*50000000000000^6373 ≤ 6219963962497^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065187727 10000000000 6219963962497 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312610157/10000000000 : ℝ), (1078270219/2000000000 : ℝ), (-2065187727/10000000000 : ℝ)] ![(1083862261389/2500000000000 : ℝ), (44205581598499/100000000000000 : ℝ), (6219963962497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312610157/10000000000 : ℝ)|^8421 ≤ (1083862261389/2500000000000 : ℝ)^6373
        have hw : |(5312610157/10000000000 : ℝ)|=(5312610157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078270219/2000000000 : ℝ)|^8421 ≤ (44205581598499/100000000000000 : ℝ)^6373
        have hw : |(1078270219/2000000000 : ℝ)|=(1078270219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065187727/10000000000 : ℝ)|^8421 ≤ (6219963962497/50000000000000 : ℝ)^6373
        have hw : |(-2065187727/10000000000 : ℝ)|=(2065187727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s6_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352696227/10000000000 : ℝ)*x 0 + (4480118497/10000000000 : ℝ)*x 1 + (4228830177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352696227/10000000000 : ℝ)^8421 ≤ (6663482894297/20000000000000 : ℝ)^6373 := by
    have hnat : (4352696227 : ℕ)^8421*20000000000000^6373 ≤ 6663482894297^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352696227 10000000000 6663482894297 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480118497/10000000000 : ℝ)^8421 ≤ (8653053650577/25000000000000 : ℝ)^6373 := by
    have hnat : (4480118497 : ℕ)^8421*25000000000000^6373 ≤ 8653053650577^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480118497 10000000000 8653053650577 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228830177/10000000000 : ℝ)^8421 ≤ (32070370912679/100000000000000 : ℝ)^6373 := by
    have hnat : (4228830177 : ℕ)^8421*100000000000000^6373 ≤ 32070370912679^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228830177 10000000000 32070370912679 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352696227/10000000000 : ℝ), (4480118497/10000000000 : ℝ), (4228830177/10000000000 : ℝ)] ![(6663482894297/20000000000000 : ℝ), (8653053650577/25000000000000 : ℝ), (32070370912679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352696227/10000000000 : ℝ)|^8421 ≤ (6663482894297/20000000000000 : ℝ)^6373
        have hw : |(4352696227/10000000000 : ℝ)|=(4352696227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480118497/10000000000 : ℝ)|^8421 ≤ (8653053650577/25000000000000 : ℝ)^6373
        have hw : |(4480118497/10000000000 : ℝ)|=(4480118497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228830177/10000000000 : ℝ)|^8421 ≤ (32070370912679/100000000000000 : ℝ)^6373
        have hw : |(4228830177/10000000000 : ℝ)|=(4228830177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11457/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2287/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2287/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2287/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2287/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2287/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2287/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2287/20000 : ℝ) ^ (2105/512 : ℝ) ≤ (6715368954796107/50000000000000000000 : ℝ) := by
    have hpowers : (2287/20000 : ℝ)^2105 ≤ (6715368954796107/50000000000000000000 : ℝ)^512 := by
      have hnat : (2287 : ℕ)^2105*50000000000000000000^512 ≤ 6715368954796107^512*20000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2287 20000 6715368954796107 50000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2287/20000 : ℝ)) (X := (6715368954796107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3531/25000 : ℝ) ^ (2105/512 : ℝ) ≤ (1600174058390631/5000000000000000000 : ℝ) := by
    have hpowers : (3531/25000 : ℝ)^2105 ≤ (1600174058390631/5000000000000000000 : ℝ)^512 := by
      have hnat : (3531 : ℕ)^2105*5000000000000000000^512 ≤ 1600174058390631^512*25000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3531 25000 1600174058390631 5000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3531/25000 : ℝ)) (X := (1600174058390631/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006715368954796107/25000000000000000000 : ℝ) ≤ (1250081660795607/1250000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (25006715368954796107/25000000000000000000 : ℝ)^512 ≤ (1250081660795607/1250000000000000 : ℝ)^2105 := by
      have hnat : (25006715368954796107 : ℕ)^512*1250000000000000^2105 ≤ 1250081660795607^2105*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006715368954796107 25000000000000000000 1250081660795607 1250000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250081660795607/1250000000000000 : ℝ)) (X := (25006715368954796107/25000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022717109538702417/50000000000000000000 : ℝ) ≤ (10001104908411503/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (50022717109538702417/50000000000000000000 : ℝ)^512 ≤ (10001104908411503/10000000000000000 : ℝ)^2105 := by
      have hnat : (50022717109538702417 : ℕ)^512*10000000000000000^2105 ≤ 10001104908411503^2105*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022717109538702417 50000000000000000000 10001104908411503 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001104908411503/10000000000000000 : ℝ)) (X := (50022717109538702417/50000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501600174058390631/2500000000000000000 : ℝ) ≤ (200031130609163/200000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (2501600174058390631/2500000000000000000 : ℝ)^512 ≤ (200031130609163/200000000000000 : ℝ)^2105 := by
      have hnat : (2501600174058390631 : ℕ)^512*200000000000000^2105 ≤ 200031130609163^2105*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501600174058390631 2500000000000000000 200031130609163 200000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200031130609163/200000000000000 : ℝ)) (X := (2501600174058390631/2500000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6715368954796107/50000000000000000000 : ℝ) ≤ ((13440714045414140447/13445000000000000000 : ℝ)+2*(451622046647/268900000000000 : ℝ)*(2287/20000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (13440714045414140447/13445000000000000000 : ℝ)+2*(451622046647/268900000000000 : ℝ)*(2287/20000 : ℝ)=(1250081660795607/1250000000000000 : ℝ) by norm_num, show 1+2*(6715368954796107/50000000000000000000 : ℝ)=(25006715368954796107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1600174058390631/5000000000000000000 : ℝ)+(6715368954796107/50000000000000000000 : ℝ) ≤ ((13440714045414140447/13445000000000000000 : ℝ)+(451622046647/268900000000000 : ℝ)*((3531/25000 : ℝ)+(2287/20000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (13440714045414140447/13445000000000000000 : ℝ)+(451622046647/268900000000000 : ℝ)*((3531/25000 : ℝ)+(2287/20000 : ℝ))=(10001104908411503/10000000000000000 : ℝ) by norm_num, show 1+(1600174058390631/5000000000000000000 : ℝ)+(6715368954796107/50000000000000000000 : ℝ)=(50022717109538702417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1600174058390631/5000000000000000000 : ℝ) ≤ ((13440714045414140447/13445000000000000000 : ℝ)+2*(451622046647/268900000000000 : ℝ)*(3531/25000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (13440714045414140447/13445000000000000000 : ℝ)+2*(451622046647/268900000000000 : ℝ)*(3531/25000 : ℝ)=(200031130609163/200000000000000 : ℝ) by norm_num, show 1+2*(1600174058390631/5000000000000000000 : ℝ)=(2501600174058390631/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13440714045414140447/13445000000000000000 : ℝ)*(X 1 0+X 2 0)+(451622046647/268900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (2287/20000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (13440714045414140447/13445000000000000000 : ℝ)) (alpha := (451622046647/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13440714045414140447/13445000000000000000 : ℝ)*(X 0 1+X 2 1)+(451622046647/268900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (2287/20000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (13440714045414140447/13445000000000000000 : ℝ)) (alpha := (451622046647/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13440714045414140447/13445000000000000000 : ℝ)*(X 0 2+X 1 2)+(451622046647/268900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (2287/20000 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (13440714045414140447/13445000000000000000 : ℝ)) (alpha := (451622046647/268900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2126409023/10000000000 : ℝ)*X 0 0+(1347916981/2500000000 : ℝ)*X 0 1+(2633412637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213777359/400000000 : ℝ)*X 1 0+(-437942729/2000000000 : ℝ)*X 1 1+(1053365041/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344433941/10000000000 : ℝ)*X 2 0+(2633412617/5000000000 : ℝ)*X 2 1+(-547428413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088171593/2500000000 : ℝ)*X 0 0+(132130919/312500000 : ℝ)*X 0 1+(2240378611/5000000000 : ℝ)*X 0 2+(1088171593/2500000000 : ℝ)*X 1 0+(132130919/312500000 : ℝ)*X 1 1+(2240378611/5000000000 : ℝ)*X 1 2+(1088171593/2500000000 : ℝ)*X 2 0+(132130919/312500000 : ℝ)*X 2 1+(2240378611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-531603449/2500000000 : ℝ)*X 0 0+(658392609/1250000000 : ℝ)*X 0 1+(1347837787/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312610197/10000000000 : ℝ)*X 1 0+(-413037577/2000000000 : ℝ)*X 1 1+(269567547/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312610157/10000000000 : ℝ)*X 2 0+(1078270219/2000000000 : ℝ)*X 2 1+(-2065187727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352696227/10000000000 : ℝ)*X 0 0+(4480118497/10000000000 : ℝ)*X 0 1+(4228830177/10000000000 : ℝ)*X 0 2+(4352696227/10000000000 : ℝ)*X 1 0+(4480118497/10000000000 : ℝ)*X 1 1+(4228830177/10000000000 : ℝ)*X 1 2+(4352696227/10000000000 : ℝ)*X 2 0+(4480118497/10000000000 : ℝ)*X 2 1+(4228830177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (473103532293965737968610323/67225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130286773/10000000000000 : ℝ)*(base19) + (1149961477/100000000000000 : ℝ)*(base23) + (54485229/100000000000000 : ℝ)*(lower2) + (82449041/50000000000000 : ℝ)*(upper3) + (69408561/100000000000000 : ℝ)*(upper5) + (1196951842240697/20000000000000 : ℝ)*(major0) + (1196951842240697/20000000000000 : ℝ)*(major1) + (1196951842240697/20000000000000 : ℝ)*(major2) + (8010118484572983/100000000000000 : ℝ)*(sp0) + (1602029804526861/20000000000000 : ℝ)*(sp1) + (4005074587770279/50000000000000 : ℝ)*(sp2) + (1979674553669901/50000000000000 : ℝ)*(sp3) + (7960232263/25000000000000 : ℝ)*(sp4) + (4688744507/25000000000000 : ℝ)*(sp7) + (395936786231783/10000000000000 : ℝ)*(f.failure) + (1602030065100407/20000000000000 : ℝ)*(f.sum) + (1620480893587/672250000000000000000000000 : ℝ)*base65 + (1930359705969921559/268900000000000000000000000000000 : ℝ)*base67 + (510187677666921559/268900000000000000000000000000000 : ℝ)*base69 + (3781526650317621559/268900000000000000000000000000000 : ℝ)*base71 + (179338460899/42015625000000000000000000 : ℝ)*base73 + (3408140863012621559/268900000000000000000000000000000 : ℝ)*base75 + (674449883880921559/268900000000000000000000000000000 : ℝ)*base77 + (1550639513820478441/268900000000000000000000000000000 : ℝ)*base80 + (6033528831183/2689000000000000000000000000 : ℝ)*base81 + (1269149/250000000000000000000 : ℝ)*base89 + (1269149/250000000000000000000 : ℝ)*base91 + (1269149/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5465531451967972973189993787/672250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216077131/12500000000000 : ℝ)*(base19) + (2035725379/100000000000000 : ℝ)*(base23) + (201831859/100000000000000 : ℝ)*(upper3) + (70680999/50000000000000 : ℝ)*(lower4) + (223041137/100000000000000 : ℝ)*(upper5) + (6015176062061593/100000000000000 : ℝ)*(major0) + (6015176062061593/100000000000000 : ℝ)*(major1) + (6015176062061593/100000000000000 : ℝ)*(major2) + (34319746379/100000000000000 : ℝ)*(sp1) + (51286962857/100000000000000 : ℝ)*(sp2) + (201271523967283/2500000000000 : ℝ)*(sp4) + (8050824910327893/100000000000000 : ℝ)*(sp5) + (8050807636003083/100000000000000 : ℝ)*(sp6) + (1989745447212481/50000000000000 : ℝ)*(sp7) + (1989745447212481/50000000000000 : ℝ)*(f.failure) + (201271523967283/2500000000000 : ℝ)*(f.sum) + (115976491020641/13445000000000000000000000000 : ℝ)*base65 + (8484151613747102071/1344500000000000000000000000000000 : ℝ)*base67 + (2076573851612897929/1344500000000000000000000000000000 : ℝ)*base70 + (22303706906310102071/1344500000000000000000000000000000 : ℝ)*base71 + (76726009089141/13445000000000000000000000000 : ℝ)*base73 + (30443932978710397929/1344500000000000000000000000000000 : ℝ)*base76 + (15433188182731102071/1344500000000000000000000000000000 : ℝ)*base77 + (10877189002803602071/1344500000000000000000000000000000 : ℝ)*base79 + (31410676958233/6722500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (11345957/1250000000000000000000 : ℝ)*base90 + (11345957/1250000000000000000000 : ℝ)*base92 + (11345957/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1228_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1228_s7_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-531605979/2500000000 : ℝ)*x 0 + (1078292017/2000000000 : ℝ)*x 1 + (5267023553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531605979/2500000000 : ℝ)^8421 ≤ (258592709739/2000000000000 : ℝ)^6373 := by
    have hnat : (531605979 : ℕ)^8421*2000000000000^6373 ≤ 258592709739^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531605979 2500000000 258592709739 2000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078292017/2000000000 : ℝ)^8421 ≤ (44206762428303/100000000000000 : ℝ)^6373 := by
    have hnat : (1078292017 : ℕ)^8421*100000000000000^6373 ≤ 44206762428303^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078292017 2000000000 44206762428303 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267023553/10000000000 : ℝ)^8421 ≤ (21431801031597/50000000000000 : ℝ)^6373 := by
    have hnat : (5267023553 : ℕ)^8421*50000000000000^6373 ≤ 21431801031597^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267023553 10000000000 21431801031597 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531605979/2500000000 : ℝ), (1078292017/2000000000 : ℝ), (5267023553/10000000000 : ℝ)] ![(258592709739/2000000000000 : ℝ), (44206762428303/100000000000000 : ℝ), (21431801031597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531605979/2500000000 : ℝ)|^8421 ≤ (258592709739/2000000000000 : ℝ)^6373
        have hw : |(-531605979/2500000000 : ℝ)|=(531605979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078292017/2000000000 : ℝ)|^8421 ≤ (44206762428303/100000000000000 : ℝ)^6373
        have hw : |(1078292017/2000000000 : ℝ)|=(1078292017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267023553/10000000000 : ℝ)|^8421 ≤ (21431801031597/50000000000000 : ℝ)^6373
        have hw : |(5267023553/10000000000 : ℝ)|=(5267023553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668047769/1250000000 : ℝ)*x 0 + (-437903949/2000000000 : ℝ)*x 1 + (5267023517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668047769/1250000000 : ℝ)^8421 ≤ (43697421606351/100000000000000 : ℝ)^6373 := by
    have hnat : (668047769 : ℕ)^8421*100000000000000^6373 ≤ 43697421606351^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668047769 1250000000 43697421606351 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437903949/2000000000 : ℝ)^8421 ≤ (839936044277/6250000000000 : ℝ)^6373 := by
    have hnat : (437903949 : ℕ)^8421*6250000000000^6373 ≤ 839936044277^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437903949 2000000000 839936044277 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267023517/10000000000 : ℝ)^8421 ≤ (21431800838037/50000000000000 : ℝ)^6373 := by
    have hnat : (5267023517 : ℕ)^8421*50000000000000^6373 ≤ 21431800838037^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267023517 10000000000 21431800838037 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668047769/1250000000 : ℝ), (-437903949/2000000000 : ℝ), (5267023517/10000000000 : ℝ)] ![(43697421606351/100000000000000 : ℝ), (839936044277/6250000000000 : ℝ), (21431800838037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668047769/1250000000 : ℝ)|^8421 ≤ (43697421606351/100000000000000 : ℝ)^6373
        have hw : |(668047769/1250000000 : ℝ)|=(668047769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437903949/2000000000 : ℝ)|^8421 ≤ (839936044277/6250000000000 : ℝ)^6373
        have hw : |(-437903949/2000000000 : ℝ)|=(437903949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267023517/10000000000 : ℝ)|^8421 ≤ (21431800838037/50000000000000 : ℝ)^6373
        have hw : |(5267023517/10000000000 : ℝ)|=(5267023517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336095547/2500000000 : ℝ)*x 0 + (526702351/1000000000 : ℝ)*x 1 + (-437903941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336095547/2500000000 : ℝ)^8421 ≤ (43697421995289/100000000000000 : ℝ)^6373 := by
    have hnat : (1336095547 : ℕ)^8421*100000000000000^6373 ≤ 43697421995289^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336095547 2500000000 43697421995289 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526702351/1000000000 : ℝ)^8421 ≤ (53579502001/125000000000 : ℝ)^6373 := by
    have hnat : (526702351 : ℕ)^8421*125000000000^6373 ≤ 53579502001^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526702351 1000000000 53579502001 125000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437903941/2000000000 : ℝ)^8421 ≤ (671948819201/5000000000000 : ℝ)^6373 := by
    have hnat : (437903941 : ℕ)^8421*5000000000000^6373 ≤ 671948819201^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437903941 2000000000 671948819201 5000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336095547/2500000000 : ℝ), (526702351/1000000000 : ℝ), (-437903941/2000000000 : ℝ)] ![(43697421995289/100000000000000 : ℝ), (53579502001/125000000000 : ℝ), (671948819201/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336095547/2500000000 : ℝ)|^8421 ≤ (43697421995289/100000000000000 : ℝ)^6373
        have hw : |(1336095547/2500000000 : ℝ)|=(1336095547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526702351/1000000000 : ℝ)|^8421 ≤ (53579502001/125000000000 : ℝ)^6373
        have hw : |(526702351/1000000000 : ℝ)|=(526702351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437903941/2000000000 : ℝ)|^8421 ≤ (671948819201/5000000000000 : ℝ)^6373
        have hw : |(-437903941/2000000000 : ℝ)|=(437903941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43526967/100000000 : ℝ)*x 0 + (1057149693/2500000000 : ℝ)*x 1 + (560043147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43526967/100000000 : ℝ)^8421 ≤ (16658709627757/50000000000000 : ℝ)^6373 := by
    have hnat : (43526967 : ℕ)^8421*50000000000000^6373 ≤ 16658709627757^6373*100000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43526967 100000000 16658709627757 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057149693/2500000000 : ℝ)^8421 ≤ (32068052064011/100000000000000 : ℝ)^6373 := by
    have hnat : (1057149693 : ℕ)^8421*100000000000000^6373 ≤ 32068052064011^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057149693 2500000000 32068052064011 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560043147/1250000000 : ℝ)^8421 ≤ (692290573229/2000000000000 : ℝ)^6373 := by
    have hnat : (560043147 : ℕ)^8421*2000000000000^6373 ≤ 692290573229^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560043147 1250000000 692290573229 2000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43526967/100000000 : ℝ), (1057149693/2500000000 : ℝ), (560043147/1250000000 : ℝ)] ![(16658709627757/50000000000000 : ℝ), (32068052064011/100000000000000 : ℝ), (692290573229/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43526967/100000000 : ℝ)|^8421 ≤ (16658709627757/50000000000000 : ℝ)^6373
        have hw : |(43526967/100000000 : ℝ)|=(43526967/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057149693/2500000000 : ℝ)|^8421 ≤ (32068052064011/100000000000000 : ℝ)^6373
        have hw : |(1057149693/2500000000 : ℝ)|=(1057149693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560043147/1250000000 : ℝ)|^8421 ≤ (692290573229/2000000000000 : ℝ)^6373
        have hw : |(560043147/1250000000 : ℝ)|=(560043147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063214301/5000000000 : ℝ)*x 0 + (658417219/1250000000 : ℝ)*x 1 + (1078228951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063214301/5000000000 : ℝ)^8421 ≤ (6464836568199/50000000000000 : ℝ)^6373 := by
    have hnat : (1063214301 : ℕ)^8421*50000000000000^6373 ≤ 6464836568199^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063214301 5000000000 6464836568199 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658417219/1250000000 : ℝ)^8421 ≤ (5358372597813/12500000000000 : ℝ)^6373 := by
    have hnat : (658417219 : ℕ)^8421*12500000000000^6373 ≤ 5358372597813^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658417219 1250000000 5358372597813 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078228951/2000000000 : ℝ)^8421 ≤ (22101673035547/50000000000000 : ℝ)^6373 := by
    have hnat : (1078228951 : ℕ)^8421*50000000000000^6373 ≤ 22101673035547^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078228951 2000000000 22101673035547 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063214301/5000000000 : ℝ), (658417219/1250000000 : ℝ), (1078228951/2000000000 : ℝ)] ![(6464836568199/50000000000000 : ℝ), (5358372597813/12500000000000 : ℝ), (22101673035547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063214301/5000000000 : ℝ)|^8421 ≤ (6464836568199/50000000000000 : ℝ)^6373
        have hw : |(-1063214301/5000000000 : ℝ)|=(1063214301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658417219/1250000000 : ℝ)|^8421 ≤ (5358372597813/12500000000000 : ℝ)^6373
        have hw : |(658417219/1250000000 : ℝ)|=(658417219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078228951/2000000000 : ℝ)|^8421 ≤ (22101673035547/50000000000000 : ℝ)^6373
        have hw : |(1078228951/2000000000 : ℝ)|=(1078228951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062532319/2000000000 : ℝ)*x 0 + (-2065397743/10000000000 : ℝ)*x 1 + (5391145609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062532319/2000000000 : ℝ)^8421 ≤ (43355045120399/100000000000000 : ℝ)^6373 := by
    have hnat : (1062532319 : ℕ)^8421*100000000000000^6373 ≤ 43355045120399^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062532319 2000000000 43355045120399 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065397743/10000000000 : ℝ)^8421 ≤ (2488319908997/20000000000000 : ℝ)^6373 := by
    have hnat : (2065397743 : ℕ)^8421*20000000000000^6373 ≤ 2488319908997^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065397743 10000000000 2488319908997 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391145609/10000000000 : ℝ)^8421 ≤ (22101677661719/50000000000000 : ℝ)^6373 := by
    have hnat : (5391145609 : ℕ)^8421*50000000000000^6373 ≤ 22101677661719^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391145609 10000000000 22101677661719 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062532319/2000000000 : ℝ), (-2065397743/10000000000 : ℝ), (5391145609/10000000000 : ℝ)] ![(43355045120399/100000000000000 : ℝ), (2488319908997/20000000000000 : ℝ), (22101677661719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062532319/2000000000 : ℝ)|^8421 ≤ (43355045120399/100000000000000 : ℝ)^6373
        have hw : |(1062532319/2000000000 : ℝ)|=(1062532319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065397743/10000000000 : ℝ)|^8421 ≤ (2488319908997/20000000000000 : ℝ)^6373
        have hw : |(-2065397743/10000000000 : ℝ)|=(2065397743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391145609/10000000000 : ℝ)|^8421 ≤ (22101677661719/50000000000000 : ℝ)^6373
        have hw : |(5391145609/10000000000 : ℝ)|=(5391145609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656330941/5000000000 : ℝ)*x 0 + (2695572519/5000000000 : ℝ)*x 1 + (-516349533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656330941/5000000000 : ℝ)^8421 ≤ (1734201928607/4000000000000 : ℝ)^6373 := by
    have hnat : (2656330941 : ℕ)^8421*4000000000000^6373 ≤ 1734201928607^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656330941 5000000000 1734201928607 4000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695572519/5000000000 : ℝ)^8421 ≤ (44203349137151/100000000000000 : ℝ)^6373 := by
    have hnat : (2695572519 : ℕ)^8421*100000000000000^6373 ≤ 44203349137151^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695572519 5000000000 44203349137151 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516349533/2500000000 : ℝ)^8421 ≤ (12441602641277/100000000000000 : ℝ)^6373 := by
    have hnat : (516349533 : ℕ)^8421*100000000000000^6373 ≤ 12441602641277^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516349533 2500000000 12441602641277 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656330941/5000000000 : ℝ), (2695572519/5000000000 : ℝ), (-516349533/2500000000 : ℝ)] ![(1734201928607/4000000000000 : ℝ), (44203349137151/100000000000000 : ℝ), (12441602641277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656330941/5000000000 : ℝ)|^8421 ≤ (1734201928607/4000000000000 : ℝ)^6373
        have hw : |(2656330941/5000000000 : ℝ)|=(2656330941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695572519/5000000000 : ℝ)|^8421 ≤ (44203349137151/100000000000000 : ℝ)^6373
        have hw : |(2695572519/5000000000 : ℝ)|=(2695572519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516349533/2500000000 : ℝ)|^8421 ≤ (12441602641277/100000000000000 : ℝ)^6373
        have hw : |(-516349533/2500000000 : ℝ)|=(516349533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s7_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176353121/5000000000 : ℝ)*x 0 + (4479710847/10000000000 : ℝ)*x 1 + (4229235339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176353121/5000000000 : ℝ)^8421 ≤ (16658757882751/50000000000000 : ℝ)^6373 := by
    have hnat : (2176353121 : ℕ)^8421*50000000000000^6373 ≤ 16658757882751^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176353121 5000000000 16658757882751 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479710847/10000000000 : ℝ)^8421 ≤ (34608053190141/100000000000000 : ℝ)^6373 := by
    have hnat : (4479710847 : ℕ)^8421*100000000000000^6373 ≤ 34608053190141^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479710847 10000000000 34608053190141 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229235339/10000000000 : ℝ)^8421 ≤ (16037215516381/50000000000000 : ℝ)^6373 := by
    have hnat : (4229235339 : ℕ)^8421*50000000000000^6373 ≤ 16037215516381^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229235339 10000000000 16037215516381 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176353121/5000000000 : ℝ), (4479710847/10000000000 : ℝ), (4229235339/10000000000 : ℝ)] ![(16658757882751/50000000000000 : ℝ), (34608053190141/100000000000000 : ℝ), (16037215516381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176353121/5000000000 : ℝ)|^8421 ≤ (16658757882751/50000000000000 : ℝ)^6373
        have hw : |(2176353121/5000000000 : ℝ)|=(2176353121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479710847/10000000000 : ℝ)|^8421 ≤ (34608053190141/100000000000000 : ℝ)^6373
        have hw : |(4479710847/10000000000 : ℝ)|=(4479710847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229235339/10000000000 : ℝ)|^8421 ≤ (16037215516381/50000000000000 : ℝ)^6373
        have hw : |(4229235339/10000000000 : ℝ)|=(4229235339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11461/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11457/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11457/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11457/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11457/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11457/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11457/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11457/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (3384322880015177/25000000000000000000 : ℝ) := by
    have hpowers : (11457/100000 : ℝ)^2105 ≤ (3384322880015177/25000000000000000000 : ℝ)^512 := by
      have hnat : (11457 : ℕ)^2105*25000000000000000000^512 ≤ 3384322880015177^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11457 100000 3384322880015177 25000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11457/100000 : ℝ)) (X := (3384322880015177/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (2105/512 : ℝ) ≤ (3974878617380759/12500000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^2105 ≤ (3974878617380759/12500000000000000000 : ℝ)^512 := by
      have hnat : (7051 : ℕ)^2105*12500000000000000000^512 ≤ 3974878617380759^512*50000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 3974878617380759 12500000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (3974878617380759/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503384322880015177/12500000000000000000 : ℝ) ≤ (2000131693744557/2000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (12503384322880015177/12500000000000000000 : ℝ)^512 ≤ (2000131693744557/2000000000000000 : ℝ)^2105 := by
      have hnat : (12503384322880015177 : ℕ)^512*2000000000000000^2105 ≤ 2000131693744557^2105*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503384322880015177 12500000000000000000 2000131693744557 2000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000131693744557/2000000000000000 : ℝ)) (X := (12503384322880015177/12500000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002266816022955339/5000000000000000000 : ℝ) ≤ (500055126401849/500000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (5002266816022955339/5000000000000000000 : ℝ)^512 ≤ (500055126401849/500000000000000 : ℝ)^2105 := by
      have hnat : (5002266816022955339 : ℕ)^512*500000000000000^2105 ≤ 500055126401849^2105*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002266816022955339 5000000000000000000 500055126401849 500000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500055126401849/500000000000000 : ℝ)) (X := (5002266816022955339/5000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253974878617380759/6250000000000000000 : ℝ) ≤ (400061863494047/400000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (6253974878617380759/6250000000000000000 : ℝ)^512 ≤ (400061863494047/400000000000000 : ℝ)^2105 := by
      have hnat : (6253974878617380759 : ℕ)^512*400000000000000^2105 ≤ 400061863494047^2105*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253974878617380759 6250000000000000000 400061863494047 400000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400061863494047/400000000000000 : ℝ)) (X := (6253974878617380759/6250000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3384322880015177/25000000000000000000 : ℝ) ≤ ((5288313294929260419/5290000000000000000 : ℝ)+2*(88811862839/52900000000000 : ℝ)*(11457/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (5288313294929260419/5290000000000000000 : ℝ)+2*(88811862839/52900000000000 : ℝ)*(11457/100000 : ℝ)=(2000131693744557/2000000000000000 : ℝ) by norm_num, show 1+2*(3384322880015177/25000000000000000000 : ℝ)=(12503384322880015177/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3974878617380759/12500000000000000000 : ℝ)+(3384322880015177/25000000000000000000 : ℝ) ≤ ((5288313294929260419/5290000000000000000 : ℝ)+(88811862839/52900000000000 : ℝ)*((7051/50000 : ℝ)+(11457/100000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (5288313294929260419/5290000000000000000 : ℝ)+(88811862839/52900000000000 : ℝ)*((7051/50000 : ℝ)+(11457/100000 : ℝ))=(500055126401849/500000000000000 : ℝ) by norm_num, show 1+(3974878617380759/12500000000000000000 : ℝ)+(3384322880015177/25000000000000000000 : ℝ)=(5002266816022955339/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3974878617380759/12500000000000000000 : ℝ) ≤ ((5288313294929260419/5290000000000000000 : ℝ)+2*(88811862839/52900000000000 : ℝ)*(7051/50000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (5288313294929260419/5290000000000000000 : ℝ)+2*(88811862839/52900000000000 : ℝ)*(7051/50000 : ℝ)=(400061863494047/400000000000000 : ℝ) by norm_num, show 1+2*(3974878617380759/12500000000000000000 : ℝ)=(6253974878617380759/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5288313294929260419/5290000000000000000 : ℝ)*(X 1 0+X 2 0)+(88811862839/52900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11457/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (5288313294929260419/5290000000000000000 : ℝ)) (alpha := (88811862839/52900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5288313294929260419/5290000000000000000 : ℝ)*(X 0 1+X 2 1)+(88811862839/52900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11457/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (5288313294929260419/5290000000000000000 : ℝ)) (alpha := (88811862839/52900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5288313294929260419/5290000000000000000 : ℝ)*(X 0 2+X 1 2)+(88811862839/52900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11457/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (5288313294929260419/5290000000000000000 : ℝ)) (alpha := (88811862839/52900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531605979/2500000000 : ℝ)*X 0 0+(1078292017/2000000000 : ℝ)*X 0 1+(5267023553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668047769/1250000000 : ℝ)*X 1 0+(-437903949/2000000000 : ℝ)*X 1 1+(5267023517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336095547/2500000000 : ℝ)*X 2 0+(526702351/1000000000 : ℝ)*X 2 1+(-437903941/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43526967/100000000 : ℝ)*X 0 0+(1057149693/2500000000 : ℝ)*X 0 1+(560043147/1250000000 : ℝ)*X 0 2+(43526967/100000000 : ℝ)*X 1 0+(1057149693/2500000000 : ℝ)*X 1 1+(560043147/1250000000 : ℝ)*X 1 2+(43526967/100000000 : ℝ)*X 2 0+(1057149693/2500000000 : ℝ)*X 2 1+(560043147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063214301/5000000000 : ℝ)*X 0 0+(658417219/1250000000 : ℝ)*X 0 1+(1078228951/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062532319/2000000000 : ℝ)*X 1 0+(-2065397743/10000000000 : ℝ)*X 1 1+(5391145609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656330941/5000000000 : ℝ)*X 2 0+(2695572519/5000000000 : ℝ)*X 2 1+(-516349533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176353121/5000000000 : ℝ)*X 0 0+(4479710847/10000000000 : ℝ)*X 0 1+(4229235339/10000000000 : ℝ)*X 0 2+(2176353121/5000000000 : ℝ)*X 1 0+(4479710847/10000000000 : ℝ)*X 1 1+(4229235339/10000000000 : ℝ)*X 1 2+(2176353121/5000000000 : ℝ)*X 2 0+(4479710847/10000000000 : ℝ)*X 2 1+(4229235339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236753118319388726361432147/26450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (839521681/50000000000000 : ℝ)*(base19) + (81965171/5000000000000 : ℝ)*(base23) + (25084639/50000000000000 : ℝ)*(lower2) + (181747683/100000000000000 : ℝ)*(upper3) + (187286547/100000000000000 : ℝ)*(upper5) + (1200861877280229/20000000000000 : ℝ)*(major0) + (1200861877280229/20000000000000 : ℝ)*(major1) + (1200861877280229/20000000000000 : ℝ)*(major2) + (4018134825446353/50000000000000 : ℝ)*(sp0) + (1004539377918459/12500000000000 : ℝ)*(sp1) + (8036315063087613/100000000000000 : ℝ)*(sp2) + (1986138077175189/50000000000000 : ℝ)*(sp3) + (5881437291/12500000000000 : ℝ)*(sp4) + (25617695247/100000000000000 : ℝ)*(sp7) + (6355682835273/160000000000 : ℝ)*(f.failure) + (4018158351195517/50000000000000 : ℝ)*(f.sum) + (1666945857307/529000000000000000000000000 : ℝ)*base66 + (1287034007686255951/105800000000000000000000000000000 : ℝ)*base67 + (1961076748243855951/105800000000000000000000000000000 : ℝ)*base69 + (434737822810344049/105800000000000000000000000000000 : ℝ)*base72 + (669218711233/264500000000000000000000000 : ℝ)*base73 + (3376169907121055951/105800000000000000000000000000000 : ℝ)*base75 + (234649562009655951/105800000000000000000000000000000 : ℝ)*base77 + (3339039506095055951/105800000000000000000000000000000 : ℝ)*base79 + (182384524653/529000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6381/4000000000000000000 : ℝ)*base90 + (6381/4000000000000000000 : ℝ)*base92 + (6381/4000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183982251804947106259456701/66125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54904631/20000000000000 : ℝ)*(base19) + (27004079/4000000000000 : ℝ)*(base23) + (139771671/100000000000000 : ℝ)*(upper3) + (6206557/20000000000000 : ℝ)*(lower4) + (1508691868003507/25000000000000 : ℝ)*(major0) + (1508691868003507/25000000000000 : ℝ)*(major1) + (1508691868003507/25000000000000 : ℝ)*(major2) + (54505600929/100000000000000 : ℝ)*(sp1) + (38733464003/100000000000000 : ℝ)*(sp2) + (20754059901/100000000000000 : ℝ)*(sp3) + (4038541383621151/50000000000000 : ℝ)*(sp4) + (4038513993559109/50000000000000 : ℝ)*(sp5) + (8077043358676323/100000000000000 : ℝ)*(sp6) + (3992431329981171/100000000000000 : ℝ)*(sp7) + (249528255252567/6250000000000 : ℝ)*(f.failure) + (4038541383621151/50000000000000 : ℝ)*(f.sum) + (6630333279909/1322500000000000000000000000 : ℝ)*base66 + (415696981401339433/132250000000000000000000000000000 : ℝ)*base67 + (780068605096839433/132250000000000000000000000000000 : ℝ)*base69 + (60531077995589433/132250000000000000000000000000000 : ℝ)*base71 + (1373166861321/1322500000000000000000000000 : ℝ)*base73 + (351095539354410567/132250000000000000000000000000000 : ℝ)*base76 + (187403489611410567/132250000000000000000000000000000 : ℝ)*base78 + (2495558253826339433/132250000000000000000000000000000 : ℝ)*base79 + (7040868280181/1322500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (343901/156250000000000000000 : ℝ)*base89 + (343901/156250000000000000000 : ℝ)*base91 + (343901/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1228_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1228_s8_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-53160749/250000000 : ℝ)*x 0 + (1078283299/2000000000 : ℝ)*x 1 + (1316765739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53160749/250000000 : ℝ)^8421 ≤ (12929684047191/100000000000000 : ℝ)^6373 := by
    have hnat : (53160749 : ℕ)^8421*100000000000000^6373 ≤ 12929684047191^6373*250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53160749 250000000 12929684047191 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078283299/2000000000 : ℝ)^8421 ≤ (44206290160467/100000000000000 : ℝ)^6373 := by
    have hnat : (1078283299 : ℕ)^8421*100000000000000^6373 ≤ 44206290160467^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078283299 2000000000 44206290160467 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316765739/2500000000 : ℝ)^8421 ≤ (2143201288867/5000000000000 : ℝ)^6373 := by
    have hnat : (1316765739 : ℕ)^8421*5000000000000^6373 ≤ 2143201288867^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316765739 2500000000 2143201288867 5000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53160749/250000000 : ℝ), (1078283299/2000000000 : ℝ), (1316765739/2500000000 : ℝ)] ![(12929684047191/100000000000000 : ℝ), (44206290160467/100000000000000 : ℝ), (2143201288867/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53160749/250000000 : ℝ)|^8421 ≤ (12929684047191/100000000000000 : ℝ)^6373
        have hw : |(-53160749/250000000 : ℝ)|=(53160749/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078283299/2000000000 : ℝ)|^8421 ≤ (44206290160467/100000000000000 : ℝ)^6373
        have hw : |(1078283299/2000000000 : ℝ)|=(1078283299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316765739/2500000000 : ℝ)|^8421 ≤ (2143201288867/5000000000000 : ℝ)^6373
        have hw : |(1316765739/2500000000 : ℝ)|=(1316765739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336092607/2500000000 : ℝ)*x 0 + (-2189483061/10000000000 : ℝ)*x 1 + (5267062963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336092607/2500000000 : ℝ)^8421 ≤ (43697294942201/100000000000000 : ℝ)^6373 := by
    have hnat : (1336092607 : ℕ)^8421*100000000000000^6373 ≤ 43697294942201^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336092607 2500000000 43697294942201 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189483061/10000000000 : ℝ)^8421 ≤ (107509433527/800000000000 : ℝ)^6373 := by
    have hnat : (2189483061 : ℕ)^8421*800000000000^6373 ≤ 107509433527^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189483061 10000000000 107509433527 800000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267062963/10000000000 : ℝ)^8421 ≤ (42864025852613/100000000000000 : ℝ)^6373 := by
    have hnat : (5267062963 : ℕ)^8421*100000000000000^6373 ≤ 42864025852613^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267062963 10000000000 42864025852613 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336092607/2500000000 : ℝ), (-2189483061/10000000000 : ℝ), (5267062963/10000000000 : ℝ)] ![(43697294942201/100000000000000 : ℝ), (107509433527/800000000000 : ℝ), (42864025852613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336092607/2500000000 : ℝ)|^8421 ≤ (43697294942201/100000000000000 : ℝ)^6373
        have hw : |(1336092607/2500000000 : ℝ)|=(1336092607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189483061/10000000000 : ℝ)|^8421 ≤ (107509433527/800000000000 : ℝ)^6373
        have hw : |(-2189483061/10000000000 : ℝ)|=(2189483061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267062963/10000000000 : ℝ)|^8421 ≤ (42864025852613/100000000000000 : ℝ)^6373
        have hw : |(5267062963/10000000000 : ℝ)|=(5267062963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672185219/5000000000 : ℝ)*x 0 + (2633531487/5000000000 : ℝ)*x 1 + (-273685379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672185219/5000000000 : ℝ)^8421 ≤ (43697295050239/100000000000000 : ℝ)^6373 := by
    have hnat : (2672185219 : ℕ)^8421*100000000000000^6373 ≤ 43697295050239^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672185219 5000000000 43697295050239 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633531487/5000000000 : ℝ)^8421 ≤ (428640259709/1000000000000 : ℝ)^6373 := by
    have hnat : (2633531487 : ℕ)^8421*1000000000000^6373 ≤ 428640259709^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633531487 5000000000 428640259709 1000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273685379/1250000000 : ℝ)^8421 ≤ (13438678955677/100000000000000 : ℝ)^6373 := by
    have hnat : (273685379 : ℕ)^8421*100000000000000^6373 ≤ 13438678955677^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273685379 1250000000 13438678955677 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672185219/5000000000 : ℝ), (2633531487/5000000000 : ℝ), (-273685379/1250000000 : ℝ)] ![(43697295050239/100000000000000 : ℝ), (428640259709/1000000000000 : ℝ), (13438678955677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672185219/5000000000 : ℝ)|^8421 ≤ (43697295050239/100000000000000 : ℝ)^6373
        have hw : |(2672185219/5000000000 : ℝ)|=(2672185219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633531487/5000000000 : ℝ)|^8421 ≤ (428640259709/1000000000000 : ℝ)^6373
        have hw : |(2633531487/5000000000 : ℝ)|=(2633531487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273685379/1250000000 : ℝ)|^8421 ≤ (13438678955677/100000000000000 : ℝ)^6373
        have hw : |(-273685379/1250000000 : ℝ)|=(273685379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352698833/10000000000 : ℝ)*x 0 + (4228682621/10000000000 : ℝ)*x 1 + (2240130379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352698833/10000000000 : ℝ)^8421 ≤ (16658720414581/50000000000000 : ℝ)^6373 := by
    have hnat : (4352698833 : ℕ)^8421*50000000000000^6373 ≤ 16658720414581^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352698833 10000000000 16658720414581 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228682621/10000000000 : ℝ)^8421 ≤ (6413778457617/20000000000000 : ℝ)^6373 := by
    have hnat : (4228682621 : ℕ)^8421*20000000000000^6373 ≤ 6413778457617^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228682621 10000000000 6413778457617 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240130379/5000000000 : ℝ)^8421 ≤ (34613666873453/100000000000000 : ℝ)^6373 := by
    have hnat : (2240130379 : ℕ)^8421*100000000000000^6373 ≤ 34613666873453^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240130379 5000000000 34613666873453 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352698833/10000000000 : ℝ), (4228682621/10000000000 : ℝ), (2240130379/5000000000 : ℝ)] ![(16658720414581/50000000000000 : ℝ), (6413778457617/20000000000000 : ℝ), (34613666873453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352698833/10000000000 : ℝ)|^8421 ≤ (16658720414581/50000000000000 : ℝ)^6373
        have hw : |(4352698833/10000000000 : ℝ)|=(4352698833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228682621/10000000000 : ℝ)|^8421 ≤ (6413778457617/20000000000000 : ℝ)^6373
        have hw : |(4228682621/10000000000 : ℝ)|=(4228682621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240130379/5000000000 : ℝ)|^8421 ≤ (34613666873453/100000000000000 : ℝ)^6373
        have hw : |(2240130379/5000000000 : ℝ)|=(2240130379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126435217/10000000000 : ℝ)*x 0 + (2633687799/5000000000 : ℝ)*x 1 + (1078220457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126435217/10000000000 : ℝ)^8421 ≤ (12929726284353/100000000000000 : ℝ)^6373 := by
    have hnat : (2126435217 : ℕ)^8421*100000000000000^6373 ≤ 12929726284353^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126435217 10000000000 12929726284353 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633687799/5000000000 : ℝ)^8421 ≤ (42867387761471/100000000000000 : ℝ)^6373 := by
    have hnat : (2633687799 : ℕ)^8421*100000000000000^6373 ≤ 42867387761471^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633687799 5000000000 42867387761471 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078220457/2000000000 : ℝ)^8421 ≤ (11050721486581/25000000000000 : ℝ)^6373 := by
    have hnat : (1078220457 : ℕ)^8421*25000000000000^6373 ≤ 11050721486581^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078220457 2000000000 11050721486581 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126435217/10000000000 : ℝ), (2633687799/5000000000 : ℝ), (1078220457/2000000000 : ℝ)] ![(12929726284353/100000000000000 : ℝ), (42867387761471/100000000000000 : ℝ), (11050721486581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126435217/10000000000 : ℝ)|^8421 ≤ (12929726284353/100000000000000 : ℝ)^6373
        have hw : |(-2126435217/10000000000 : ℝ)|=(2126435217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633687799/5000000000 : ℝ)|^8421 ≤ (42867387761471/100000000000000 : ℝ)^6373
        have hw : |(2633687799/5000000000 : ℝ)|=(2633687799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078220457/2000000000 : ℝ)|^8421 ≤ (11050721486581/25000000000000 : ℝ)^6373
        have hw : |(1078220457/2000000000 : ℝ)|=(1078220457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312671409/10000000000 : ℝ)*x 0 + (-1032721707/5000000000 : ℝ)*x 1 + (336943893/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312671409/10000000000 : ℝ)^8421 ≤ (43355150946653/100000000000000 : ℝ)^6373 := by
    have hnat : (5312671409 : ℕ)^8421*100000000000000^6373 ≤ 43355150946653^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312671409 10000000000 43355150946653 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032721707/5000000000 : ℝ)^8421 ≤ (12441963070027/100000000000000 : ℝ)^6373 := by
    have hnat : (1032721707 : ℕ)^8421*100000000000000^6373 ≤ 12441963070027^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032721707 5000000000 12441963070027 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336943893/625000000 : ℝ)^8421 ≤ (44202885978827/100000000000000 : ℝ)^6373 := by
    have hnat : (336943893 : ℕ)^8421*100000000000000^6373 ≤ 44202885978827^6373*625000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336943893 625000000 44202885978827 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312671409/10000000000 : ℝ), (-1032721707/5000000000 : ℝ), (336943893/625000000 : ℝ)] ![(43355150946653/100000000000000 : ℝ), (12441963070027/100000000000000 : ℝ), (44202885978827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312671409/10000000000 : ℝ)|^8421 ≤ (43355150946653/100000000000000 : ℝ)^6373
        have hw : |(5312671409/10000000000 : ℝ)|=(5312671409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1032721707/5000000000 : ℝ)|^8421 ≤ (12441963070027/100000000000000 : ℝ)^6373
        have hw : |(-1032721707/5000000000 : ℝ)|=(1032721707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336943893/625000000 : ℝ)|^8421 ≤ (44202885978827/100000000000000 : ℝ)^6373
        have hw : |(336943893/625000000 : ℝ)|=(336943893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062534099/2000000000 : ℝ)*x 0 + (5391102101/10000000000 : ℝ)*x 1 + (-413088981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062534099/2000000000 : ℝ)^8421 ≤ (10838785272703/25000000000000 : ℝ)^6373 := by
    have hnat : (1062534099 : ℕ)^8421*25000000000000^6373 ≤ 10838785272703^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062534099 2000000000 10838785272703 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391102101/10000000000 : ℝ)^8421 ≤ (884057679057/2000000000000 : ℝ)^6373 := by
    have hnat : (5391102101 : ℕ)^8421*2000000000000^6373 ≤ 884057679057^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391102101 10000000000 884057679057 2000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413088981/2000000000 : ℝ)^8421 ≤ (2488394987581/20000000000000 : ℝ)^6373 := by
    have hnat : (413088981 : ℕ)^8421*20000000000000^6373 ≤ 2488394987581^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413088981 2000000000 2488394987581 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062534099/2000000000 : ℝ), (5391102101/10000000000 : ℝ), (-413088981/2000000000 : ℝ)] ![(10838785272703/25000000000000 : ℝ), (884057679057/2000000000000 : ℝ), (2488394987581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062534099/2000000000 : ℝ)|^8421 ≤ (10838785272703/25000000000000 : ℝ)^6373
        have hw : |(1062534099/2000000000 : ℝ)|=(1062534099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391102101/10000000000 : ℝ)|^8421 ≤ (884057679057/2000000000000 : ℝ)^6373
        have hw : |(5391102101/10000000000 : ℝ)|=(5391102101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413088981/2000000000 : ℝ)|^8421 ≤ (2488394987581/20000000000000 : ℝ)^6373
        have hw : |(-413088981/2000000000 : ℝ)|=(413088981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s8_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870541513/2000000000 : ℝ)*x 0 + (4479627423/10000000000 : ℝ)*x 1 + (528664873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870541513/2000000000 : ℝ)^8421 ≤ (16658764573317/50000000000000 : ℝ)^6373 := by
    have hnat : (870541513 : ℕ)^8421*50000000000000^6373 ≤ 16658764573317^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870541513 2000000000 16658764573317 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479627423/10000000000 : ℝ)^8421 ≤ (34607201588193/100000000000000 : ℝ)^6373 := by
    have hnat : (4479627423 : ℕ)^8421*100000000000000^6373 ≤ 34607201588193^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479627423 10000000000 34607201588193 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528664873/1250000000 : ℝ)^8421 ≤ (32075269253157/100000000000000 : ℝ)^6373 := by
    have hnat : (528664873 : ℕ)^8421*100000000000000^6373 ≤ 32075269253157^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528664873 1250000000 32075269253157 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870541513/2000000000 : ℝ), (4479627423/10000000000 : ℝ), (528664873/1250000000 : ℝ)] ![(16658764573317/50000000000000 : ℝ), (34607201588193/100000000000000 : ℝ), (32075269253157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870541513/2000000000 : ℝ)|^8421 ≤ (16658764573317/50000000000000 : ℝ)^6373
        have hw : |(870541513/2000000000 : ℝ)|=(870541513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479627423/10000000000 : ℝ)|^8421 ≤ (34607201588193/100000000000000 : ℝ)^6373
        have hw : |(4479627423/10000000000 : ℝ)|=(4479627423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528664873/1250000000 : ℝ)|^8421 ≤ (32075269253157/100000000000000 : ℝ)^6373
        have hw : |(528664873/1250000000 : ℝ)|=(528664873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5731/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11461/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (13556733427521839/100000000000000000000 : ℝ) := by
    have hpowers : (11461/100000 : ℝ)^2105 ≤ (13556733427521839/100000000000000000000 : ℝ)^512 := by
      have hnat : (11461 : ℕ)^2105*100000000000000000000^512 ≤ 13556733427521839^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11461 100000 13556733427521839 100000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11461/100000 : ℝ)) (X := (13556733427521839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (15876350352893369/50000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^2105 ≤ (15876350352893369/50000000000000000000 : ℝ)^512 := by
      have hnat : (14097 : ℕ)^2105*50000000000000000000^512 ≤ 15876350352893369^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 15876350352893369 50000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (15876350352893369/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013556733427521839/50000000000000000000 : ℝ) ≤ (10000659414301511/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (50013556733427521839/50000000000000000000 : ℝ)^512 ≤ (10000659414301511/10000000000000000 : ℝ)^2105 := by
      have hnat : (50013556733427521839 : ℕ)^512*10000000000000000^2105 ≤ 10000659414301511^2105*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013556733427521839 50000000000000000000 10000659414301511 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000659414301511/10000000000000000 : ℝ)) (X := (50013556733427521839/50000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045309434133308577/100000000000000000000 : ℝ) ≤ (10001101874304003/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (100045309434133308577/100000000000000000000 : ℝ)^512 ≤ (10001101874304003/10000000000000000 : ℝ)^2105 := by
      have hnat : (100045309434133308577 : ℕ)^512*10000000000000000^2105 ≤ 10001101874304003^2105*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045309434133308577 100000000000000000000 10001101874304003 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001101874304003/10000000000000000 : ℝ)) (X := (100045309434133308577/100000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015876350352893369/25000000000000000000 : ℝ) ≤ (2000308866861299/2000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (25015876350352893369/25000000000000000000 : ℝ)^512 ≤ (2000308866861299/2000000000000000 : ℝ)^2105 := by
      have hnat : (25015876350352893369 : ℕ)^512*2000000000000000^2105 ≤ 2000308866861299^2105*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015876350352893369 25000000000000000000 2000308866861299 2000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000308866861299/2000000000000000 : ℝ)) (X := (25015876350352893369/25000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13556733427521839/100000000000000000000 : ℝ) ≤ ((6587899036980415343/6590000000000000000 : ℝ)+2*(110615000623/65900000000000 : ℝ)*(11461/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (6587899036980415343/6590000000000000000 : ℝ)+2*(110615000623/65900000000000 : ℝ)*(11461/100000 : ℝ)=(10000659414301511/10000000000000000 : ℝ) by norm_num, show 1+2*(13556733427521839/100000000000000000000 : ℝ)=(50013556733427521839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15876350352893369/50000000000000000000 : ℝ)+(13556733427521839/100000000000000000000 : ℝ) ≤ ((6587899036980415343/6590000000000000000 : ℝ)+(110615000623/65900000000000 : ℝ)*((14097/100000 : ℝ)+(11461/100000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (6587899036980415343/6590000000000000000 : ℝ)+(110615000623/65900000000000 : ℝ)*((14097/100000 : ℝ)+(11461/100000 : ℝ))=(10001101874304003/10000000000000000 : ℝ) by norm_num, show 1+(15876350352893369/50000000000000000000 : ℝ)+(13556733427521839/100000000000000000000 : ℝ)=(100045309434133308577/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15876350352893369/50000000000000000000 : ℝ) ≤ ((6587899036980415343/6590000000000000000 : ℝ)+2*(110615000623/65900000000000 : ℝ)*(14097/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (6587899036980415343/6590000000000000000 : ℝ)+2*(110615000623/65900000000000 : ℝ)*(14097/100000 : ℝ)=(2000308866861299/2000000000000000 : ℝ) by norm_num, show 1+2*(15876350352893369/50000000000000000000 : ℝ)=(25015876350352893369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6587899036980415343/6590000000000000000 : ℝ)*(X 1 0+X 2 0)+(110615000623/65900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11461/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (6587899036980415343/6590000000000000000 : ℝ)) (alpha := (110615000623/65900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6587899036980415343/6590000000000000000 : ℝ)*(X 0 1+X 2 1)+(110615000623/65900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11461/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (6587899036980415343/6590000000000000000 : ℝ)) (alpha := (110615000623/65900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6587899036980415343/6590000000000000000 : ℝ)*(X 0 2+X 1 2)+(110615000623/65900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11461/100000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (6587899036980415343/6590000000000000000 : ℝ)) (alpha := (110615000623/65900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53160749/250000000 : ℝ)*X 0 0+(1078283299/2000000000 : ℝ)*X 0 1+(1316765739/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336092607/2500000000 : ℝ)*X 1 0+(-2189483061/10000000000 : ℝ)*X 1 1+(5267062963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672185219/5000000000 : ℝ)*X 2 0+(2633531487/5000000000 : ℝ)*X 2 1+(-273685379/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352698833/10000000000 : ℝ)*X 0 0+(4228682621/10000000000 : ℝ)*X 0 1+(2240130379/5000000000 : ℝ)*X 0 2+(4352698833/10000000000 : ℝ)*X 1 0+(4228682621/10000000000 : ℝ)*X 1 1+(2240130379/5000000000 : ℝ)*X 1 2+(4352698833/10000000000 : ℝ)*X 2 0+(4228682621/10000000000 : ℝ)*X 2 1+(2240130379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2126435217/10000000000 : ℝ)*X 0 0+(2633687799/5000000000 : ℝ)*X 0 1+(1078220457/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312671409/10000000000 : ℝ)*X 1 0+(-1032721707/5000000000 : ℝ)*X 1 1+(336943893/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062534099/2000000000 : ℝ)*X 2 0+(5391102101/10000000000 : ℝ)*X 2 1+(-413088981/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870541513/2000000000 : ℝ)*X 0 0+(4479627423/10000000000 : ℝ)*X 0 1+(528664873/1250000000 : ℝ)*X 0 2+(870541513/2000000000 : ℝ)*X 1 0+(4479627423/10000000000 : ℝ)*X 1 1+(528664873/1250000000 : ℝ)*X 1 2+(870541513/2000000000 : ℝ)*X 2 0+(4479627423/10000000000 : ℝ)*X 2 1+(528664873/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1902792667623213117372897/257421875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1446574973/100000000000000 : ℝ)*(base19) + (272320331/20000000000000 : ℝ)*(base23) + (53454561/100000000000000 : ℝ)*(lower2) + (170807527/100000000000000 : ℝ)*(upper3) + (146909649/100000000000000 : ℝ)*(upper5) + (18775969356947/312500000000 : ℝ)*(major0) + (18775969356947/312500000000 : ℝ)*(major1) + (18775969356947/312500000000 : ℝ)*(major2) + (4020814827533941/50000000000000 : ℝ)*(sp0) + (321666803538941/4000000000000 : ℝ)*(sp1) + (8041670173446843/100000000000000 : ℝ)*(sp2) + (496865972857153/12500000000000 : ℝ)*(sp3) + (8375996123/20000000000000 : ℝ)*(sp4) + (20824149391/100000000000000 : ℝ)*(sp7) + (496868575875827/12500000000000 : ℝ)*(f.failure) + (4020835767524249/50000000000000 : ℝ)*(f.sum) + (436727242251/164750000000000000000000000 : ℝ)*base66 + (2278130612485777/1029687500000000000000000000000 : ℝ)*base68 + (1400352426091837/257421875000000000000000000000 : ℝ)*base69 + (6996947891906951/514843750000000000000000000000 : ℝ)*base72 + (12009027287/5148437500000000000000000 : ℝ)*base73 + (1577408039356951/514843750000000000000000000000 : ℝ)*base76 + (6988346522582973/1029687500000000000000000000000 : ℝ)*base77 + (1468771125740019/128710937500000000000000000000 : ℝ)*base80 + (117102970383/20593750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3799681/312500000000000000000 : ℝ)*base89 + (3799681/312500000000000000000 : ℝ)*base91 + (3799681/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87422163999087194466886983/32950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85082493/50000000000000 : ℝ)*(base19) + (341694017/100000000000000 : ℝ)*(upper1) + (389058129/50000000000000 : ℝ)*(upper2) + (318696267/100000000000000 : ℝ)*(upper3) + (37603759/100000000000000 : ℝ)*(lower4) + (603873070499827/10000000000000 : ℝ)*(major0) + (603873070499827/10000000000000 : ℝ)*(major1) + (603873070499827/10000000000000 : ℝ)*(major2) + (44434633413/100000000000000 : ℝ)*(sp0) + (26403480491/50000000000000 : ℝ)*(sp1) + (1616468565300001/20000000000000 : ℝ)*(sp4) + (161646685680149/2000000000000 : ℝ)*(sp5) + (4041193630566709/50000000000000 : ℝ)*(sp6) + (39950740604239/1000000000000 : ℝ)*(sp7) + (39950740604239/1000000000000 : ℝ)*(f.failure) + (4041193630566709/50000000000000 : ℝ)*(f.sum) + (5728829861277/659000000000000000000000000 : ℝ)*base65 + (67935922445754339/65900000000000000000000000000000 : ℝ)*base68 + (1585761779045661/65900000000000000000000000000000 : ℝ)*base69 + (728135679459654339/65900000000000000000000000000000 : ℝ)*base72 + (82742681737/32950000000000000000000000 : ℝ)*base74 + (408703110422345661/65900000000000000000000000000000 : ℝ)*base75 + (1371218494227254339/65900000000000000000000000000000 : ℝ)*base78 + (15933296204454339/65900000000000000000000000000000 : ℝ)*base80 + (1005231055269/82375000000000000000000000 : ℝ)*base81 + (188117/25000000000000000000 : ℝ)*base89 + (188117/25000000000000000000 : ℝ)*base91 + (188117/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1228_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1228_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1228_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1228_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1228_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
