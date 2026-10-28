-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:38.19375+00:00
-- url     : https://prove2.me/submissions/1da71bc1-853c-4a13-b9f3-1debefd7297c

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
theorem support_rectangle_w1275_s6_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65727833/312500000 : ℝ)*x 0 + (108324159/200000000 : ℝ)*x 1 + (5242265927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65727833/312500000 : ℝ)^4235 ≤ (12792909432409/100000000000000 : ℝ)^3211 := by
    have hnat : (65727833 : ℕ)^4235*100000000000000^3211 ≤ 12792909432409^3211*312500000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65727833 312500000 12792909432409 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108324159/200000000 : ℝ)^4235 ≤ (44542005542941/100000000000000 : ℝ)^3211 := by
    have hnat : (108324159 : ℕ)^4235*100000000000000^3211 ≤ 44542005542941^3211*200000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108324159 200000000 44542005542941 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242265927/10000000000 : ℝ)^4235 ≤ (10666271251519/25000000000000 : ℝ)^3211 := by
    have hnat : (5242265927 : ℕ)^4235*25000000000000^3211 ≤ 10666271251519^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242265927 10000000000 10666271251519 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65727833/312500000 : ℝ), (108324159/200000000 : ℝ), (5242265927/10000000000 : ℝ)] ![(12792909432409/100000000000000 : ℝ), (44542005542941/100000000000000 : ℝ), (10666271251519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65727833/312500000 : ℝ)|^4235 ≤ (12792909432409/100000000000000 : ℝ)^3211
        have hw : |(-65727833/312500000 : ℝ)|=(65727833/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108324159/200000000 : ℝ)|^4235 ≤ (44542005542941/100000000000000 : ℝ)^3211
        have hw : |(108324159/200000000 : ℝ)|=(108324159/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242265927/10000000000 : ℝ)|^4235 ≤ (10666271251519/25000000000000 : ℝ)^3211
        have hw : |(5242265927/10000000000 : ℝ)|=(5242265927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350051899/10000000000 : ℝ)*x 0 + (-2191974031/10000000000 : ℝ)*x 1 + (5242265923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350051899/10000000000 : ℝ)^4235 ≤ (43825848787889/100000000000000 : ℝ)^3211 := by
    have hnat : (5350051899 : ℕ)^4235*100000000000000^3211 ≤ 43825848787889^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350051899 10000000000 43825848787889 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191974031/10000000000 : ℝ)^4235 ≤ (13509066240951/100000000000000 : ℝ)^3211 := by
    have hnat : (2191974031 : ℕ)^4235*100000000000000^3211 ≤ 13509066240951^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191974031 10000000000 13509066240951 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242265923/10000000000 : ℝ)^4235 ≤ (42665084963139/100000000000000 : ℝ)^3211 := by
    have hnat : (5242265923 : ℕ)^4235*100000000000000^3211 ≤ 42665084963139^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242265923 10000000000 42665084963139 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350051899/10000000000 : ℝ), (-2191974031/10000000000 : ℝ), (5242265923/10000000000 : ℝ)] ![(43825848787889/100000000000000 : ℝ), (13509066240951/100000000000000 : ℝ), (42665084963139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350051899/10000000000 : ℝ)|^4235 ≤ (43825848787889/100000000000000 : ℝ)^3211
        have hw : |(5350051899/10000000000 : ℝ)|=(5350051899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191974031/10000000000 : ℝ)|^4235 ≤ (13509066240951/100000000000000 : ℝ)^3211
        have hw : |(-2191974031/10000000000 : ℝ)|=(2191974031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242265923/10000000000 : ℝ)|^4235 ≤ (42665084963139/100000000000000 : ℝ)^3211
        have hw : |(5242265923/10000000000 : ℝ)|=(5242265923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53500519/100000000 : ℝ)*x 0 + (2621132961/5000000000 : ℝ)*x 1 + (-219197403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53500519/100000000 : ℝ)^4235 ≤ (43825848798693/100000000000000 : ℝ)^3211 := by
    have hnat : (53500519 : ℕ)^4235*100000000000000^3211 ≤ 43825848798693^3211*100000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53500519 100000000 43825848798693 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621132961/5000000000 : ℝ)^4235 ≤ (8533016990481/20000000000000 : ℝ)^3211 := by
    have hnat : (2621132961 : ℕ)^4235*20000000000000^3211 ≤ 8533016990481^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621132961 5000000000 8533016990481 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219197403/1000000000 : ℝ)^4235 ≤ (13509066232823/100000000000000 : ℝ)^3211 := by
    have hnat : (219197403 : ℕ)^4235*100000000000000^3211 ≤ 13509066232823^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219197403 1000000000 13509066232823 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53500519/100000000 : ℝ), (2621132961/5000000000 : ℝ), (-219197403/1000000000 : ℝ)] ![(43825848798693/100000000000000 : ℝ), (8533016990481/20000000000000 : ℝ), (13509066232823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53500519/100000000 : ℝ)|^4235 ≤ (43825848798693/100000000000000 : ℝ)^3211
        have hw : |(53500519/100000000 : ℝ)|=(53500519/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621132961/5000000000 : ℝ)|^4235 ≤ (8533016990481/20000000000000 : ℝ)^3211
        have hw : |(2621132961/5000000000 : ℝ)|=(2621132961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219197403/1000000000 : ℝ)|^4235 ≤ (13509066232823/100000000000000 : ℝ)^3211
        have hw : |(-219197403/1000000000 : ℝ)|=(219197403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434444261/1000000000 : ℝ)*x 0 + (2085176699/5000000000 : ℝ)*x 1 + (4525524729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434444261/1000000000 : ℝ)^4235 ≤ (8325491506103/25000000000000 : ℝ)^3211 := by
    have hnat : (434444261 : ℕ)^4235*25000000000000^3211 ≤ 8325491506103^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434444261 1000000000 8325491506103 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085176699/5000000000 : ℝ)^4235 ≤ (3944160371783/12500000000000 : ℝ)^3211 := by
    have hnat : (2085176699 : ℕ)^4235*12500000000000^3211 ≤ 3944160371783^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085176699 5000000000 3944160371783 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525524729/10000000000 : ℝ)^4235 ≤ (3514475098829/10000000000000 : ℝ)^3211 := by
    have hnat : (4525524729 : ℕ)^4235*10000000000000^3211 ≤ 3514475098829^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525524729 10000000000 3514475098829 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434444261/1000000000 : ℝ), (2085176699/5000000000 : ℝ), (4525524729/10000000000 : ℝ)] ![(8325491506103/25000000000000 : ℝ), (3944160371783/12500000000000 : ℝ), (3514475098829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434444261/1000000000 : ℝ)|^4235 ≤ (8325491506103/25000000000000 : ℝ)^3211
        have hw : |(434444261/1000000000 : ℝ)|=(434444261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085176699/5000000000 : ℝ)|^4235 ≤ (3944160371783/12500000000000 : ℝ)^3211
        have hw : |(2085176699/5000000000 : ℝ)|=(2085176699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525524729/10000000000 : ℝ)|^4235 ≤ (3514475098829/10000000000000 : ℝ)^3211
        have hw : |(4525524729/10000000000 : ℝ)|=(4525524729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051651823/5000000000 : ℝ)*x 0 + (2621442913/5000000000 : ℝ)*x 1 + (5415584841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051651823/5000000000 : ℝ)^4235 ≤ (1599126704801/12500000000000 : ℝ)^3211 := by
    have hnat : (1051651823 : ℕ)^4235*12500000000000^3211 ≤ 1599126704801^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051651823 5000000000 1599126704801 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621442913/5000000000 : ℝ)^4235 ≤ (42671739205321/100000000000000 : ℝ)^3211 := by
    have hnat : (2621442913 : ℕ)^4235*100000000000000^3211 ≤ 42671739205321^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621442913 5000000000 42671739205321 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415584841/10000000000 : ℝ)^4235 ≤ (22267623573717/50000000000000 : ℝ)^3211 := by
    have hnat : (5415584841 : ℕ)^4235*50000000000000^3211 ≤ 22267623573717^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415584841 10000000000 22267623573717 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051651823/5000000000 : ℝ), (2621442913/5000000000 : ℝ), (5415584841/10000000000 : ℝ)] ![(1599126704801/12500000000000 : ℝ), (42671739205321/100000000000000 : ℝ), (22267623573717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051651823/5000000000 : ℝ)|^4235 ≤ (1599126704801/12500000000000 : ℝ)^3211
        have hw : |(-1051651823/5000000000 : ℝ)|=(1051651823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621442913/5000000000 : ℝ)|^4235 ≤ (42671739205321/100000000000000 : ℝ)^3211
        have hw : |(2621442913/5000000000 : ℝ)|=(2621442913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415584841/10000000000 : ℝ)|^4235 ≤ (22267623573717/50000000000000 : ℝ)^3211
        have hw : |(5415584841/10000000000 : ℝ)|=(5415584841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326403863/2500000000 : ℝ)*x 0 + (-504663781/2500000000 : ℝ)*x 1 + (5415584853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326403863/2500000000 : ℝ)^4235 ≤ (8669278694639/20000000000000 : ℝ)^3211 := by
    have hnat : (1326403863 : ℕ)^4235*20000000000000^3211 ≤ 8669278694639^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326403863 2500000000 8669278694639 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504663781/2500000000 : ℝ)^4235 ≤ (12118359235221/100000000000000 : ℝ)^3211 := by
    have hnat : (504663781 : ℕ)^4235*100000000000000^3211 ≤ 12118359235221^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504663781 2500000000 12118359235221 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415584853/10000000000 : ℝ)^4235 ≤ (22267623638793/50000000000000 : ℝ)^3211 := by
    have hnat : (5415584853 : ℕ)^4235*50000000000000^3211 ≤ 22267623638793^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415584853 10000000000 22267623638793 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326403863/2500000000 : ℝ), (-504663781/2500000000 : ℝ), (5415584853/10000000000 : ℝ)] ![(8669278694639/20000000000000 : ℝ), (12118359235221/100000000000000 : ℝ), (22267623638793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326403863/2500000000 : ℝ)|^4235 ≤ (8669278694639/20000000000000 : ℝ)^3211
        have hw : |(1326403863/2500000000 : ℝ)|=(1326403863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504663781/2500000000 : ℝ)|^4235 ≤ (12118359235221/100000000000000 : ℝ)^3211
        have hw : |(-504663781/2500000000 : ℝ)|=(504663781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415584853/10000000000 : ℝ)|^4235 ≤ (22267623638793/50000000000000 : ℝ)^3211
        have hw : |(5415584853/10000000000 : ℝ)|=(5415584853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305615433/10000000000 : ℝ)*x 0 + (2707792447/5000000000 : ℝ)*x 1 + (-1009327547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305615433/10000000000 : ℝ)^4235 ≤ (2709149579279/6250000000000 : ℝ)^3211 := by
    have hnat : (5305615433 : ℕ)^4235*6250000000000^3211 ≤ 2709149579279^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305615433 10000000000 2709149579279 6250000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707792447/5000000000 : ℝ)^4235 ≤ (22267623861137/50000000000000 : ℝ)^3211 := by
    have hnat : (2707792447 : ℕ)^4235*50000000000000^3211 ≤ 22267623861137^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707792447 5000000000 22267623861137 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009327547/5000000000 : ℝ)^4235 ≤ (3029589749423/25000000000000 : ℝ)^3211 := by
    have hnat : (1009327547 : ℕ)^4235*25000000000000^3211 ≤ 3029589749423^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009327547 5000000000 3029589749423 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305615433/10000000000 : ℝ), (2707792447/5000000000 : ℝ), (-1009327547/5000000000 : ℝ)] ![(2709149579279/6250000000000 : ℝ), (22267623861137/50000000000000 : ℝ), (3029589749423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305615433/10000000000 : ℝ)|^4235 ≤ (2709149579279/6250000000000 : ℝ)^3211
        have hw : |(5305615433/10000000000 : ℝ)|=(5305615433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707792447/5000000000 : ℝ)|^4235 ≤ (22267623861137/50000000000000 : ℝ)^3211
        have hw : |(2707792447/5000000000 : ℝ)|=(2707792447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1009327547/5000000000 : ℝ)|^4235 ≤ (3029589749423/25000000000000 : ℝ)^3211
        have hw : |(-1009327547/5000000000 : ℝ)|=(1009327547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s6_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543058633/1250000000 : ℝ)*x 0 + (2262129493/5000000000 : ℝ)*x 1 + (834325129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543058633/1250000000 : ℝ)^4235 ≤ (33302233473233/100000000000000 : ℝ)^3211 := by
    have hnat : (543058633 : ℕ)^4235*100000000000000^3211 ≤ 33302233473233^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543058633 1250000000 33302233473233 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262129493/5000000000 : ℝ)^4235 ≤ (35131787233683/100000000000000 : ℝ)^3211 := by
    have hnat : (2262129493 : ℕ)^4235*100000000000000^3211 ≤ 35131787233683^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262129493 5000000000 35131787233683 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834325129/2000000000 : ℝ)^4235 ≤ (315659792797/1000000000000 : ℝ)^3211 := by
    have hnat : (834325129 : ℕ)^4235*1000000000000^3211 ≤ 315659792797^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834325129 2000000000 315659792797 1000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543058633/1250000000 : ℝ), (2262129493/5000000000 : ℝ), (834325129/2000000000 : ℝ)] ![(33302233473233/100000000000000 : ℝ), (35131787233683/100000000000000 : ℝ), (315659792797/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543058633/1250000000 : ℝ)|^4235 ≤ (33302233473233/100000000000000 : ℝ)^3211
        have hw : |(543058633/1250000000 : ℝ)|=(543058633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262129493/5000000000 : ℝ)|^4235 ≤ (35131787233683/100000000000000 : ℝ)^3211
        have hw : |(2262129493/5000000000 : ℝ)|=(2262129493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834325129/2000000000 : ℝ)|^4235 ≤ (315659792797/1000000000000 : ℝ)^3211
        have hw : |(834325129/2000000000 : ℝ)|=(834325129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10981/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10969/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (10747702999810623/100000000000000000000 : ℝ) := by
    have hpowers : (10969/100000 : ℝ)^2117 ≤ (10747702999810623/100000000000000000000 : ℝ)^512 := by
      have hnat : (10969 : ℕ)^2117*100000000000000000000^512 ≤ 10747702999810623^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10969 100000 10747702999810623 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10969/100000 : ℝ)) (X := (10747702999810623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3669/25000 : ℝ) ^ (2117/512 : ℝ) ≤ (17909694710485761/50000000000000000000 : ℝ) := by
    have hpowers : (3669/25000 : ℝ)^2117 ≤ (17909694710485761/50000000000000000000 : ℝ)^512 := by
      have hnat : (3669 : ℕ)^2117*50000000000000000000^512 ≤ 17909694710485761^512*25000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3669 25000 17909694710485761 50000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3669/25000 : ℝ)) (X := (17909694710485761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010747702999810623/50000000000000000000 : ℝ) ≤ (5000259913821581/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50010747702999810623/50000000000000000000 : ℝ)^512 ≤ (5000259913821581/5000000000000000 : ℝ)^2117 := by
      have hnat : (50010747702999810623 : ℕ)^512*5000000000000000^2117 ≤ 5000259913821581^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010747702999810623 50000000000000000000 5000259913821581 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000259913821581/5000000000000000 : ℝ)) (X := (50010747702999810623/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009313418484156429/20000000000000000000 : ℝ) ≤ (5000563017093171/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (20009313418484156429/20000000000000000000 : ℝ)^512 ≤ (5000563017093171/5000000000000000 : ℝ)^2117 := by
      have hnat : (20009313418484156429 : ℕ)^512*5000000000000000^2117 ≤ 5000563017093171^2117*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009313418484156429 20000000000000000000 5000563017093171 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000563017093171/5000000000000000 : ℝ)) (X := (20009313418484156429/20000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017909694710485761/25000000000000000000 : ℝ) ≤ (5000866120364761/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25017909694710485761/25000000000000000000 : ℝ)^512 ≤ (5000866120364761/5000000000000000 : ℝ)^2117 := by
      have hnat : (25017909694710485761 : ℕ)^512*5000000000000000^2117 ≤ 5000866120364761^2117*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017909694710485761 25000000000000000000 5000866120364761 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000866120364761/5000000000000000 : ℝ)) (X := (25017909694710485761/25000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10747702999810623/100000000000000000000 : ℝ) ≤ ((18529314020964459347/18535000000000000000 : ℝ)+2*(30310327159/18535000000000 : ℝ)*(10969/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (18529314020964459347/18535000000000000000 : ℝ)+2*(30310327159/18535000000000 : ℝ)*(10969/100000 : ℝ)=(5000259913821581/5000000000000000 : ℝ) by norm_num, show 1+2*(10747702999810623/100000000000000000000 : ℝ)=(50010747702999810623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17909694710485761/50000000000000000000 : ℝ)+(10747702999810623/100000000000000000000 : ℝ) ≤ ((18529314020964459347/18535000000000000000 : ℝ)+(30310327159/18535000000000 : ℝ)*((3669/25000 : ℝ)+(10969/100000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (18529314020964459347/18535000000000000000 : ℝ)+(30310327159/18535000000000 : ℝ)*((3669/25000 : ℝ)+(10969/100000 : ℝ))=(5000563017093171/5000000000000000 : ℝ) by norm_num, show 1+(17909694710485761/50000000000000000000 : ℝ)+(10747702999810623/100000000000000000000 : ℝ)=(20009313418484156429/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17909694710485761/50000000000000000000 : ℝ) ≤ ((18529314020964459347/18535000000000000000 : ℝ)+2*(30310327159/18535000000000 : ℝ)*(3669/25000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (18529314020964459347/18535000000000000000 : ℝ)+2*(30310327159/18535000000000 : ℝ)*(3669/25000 : ℝ)=(5000866120364761/5000000000000000 : ℝ) by norm_num, show 1+2*(17909694710485761/50000000000000000000 : ℝ)=(25017909694710485761/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18529314020964459347/18535000000000000000 : ℝ)*(X 1 0+X 2 0)+(30310327159/18535000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (18529314020964459347/18535000000000000000 : ℝ)) (alpha := (30310327159/18535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18529314020964459347/18535000000000000000 : ℝ)*(X 0 1+X 2 1)+(30310327159/18535000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (18529314020964459347/18535000000000000000 : ℝ)) (alpha := (30310327159/18535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18529314020964459347/18535000000000000000 : ℝ)*(X 0 2+X 1 2)+(30310327159/18535000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10969/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (18529314020964459347/18535000000000000000 : ℝ)) (alpha := (30310327159/18535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65727833/312500000 : ℝ)*X 0 0+(108324159/200000000 : ℝ)*X 0 1+(5242265927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350051899/10000000000 : ℝ)*X 1 0+(-2191974031/10000000000 : ℝ)*X 1 1+(5242265923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53500519/100000000 : ℝ)*X 2 0+(2621132961/5000000000 : ℝ)*X 2 1+(-219197403/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434444261/1000000000 : ℝ)*X 0 0+(2085176699/5000000000 : ℝ)*X 0 1+(4525524729/10000000000 : ℝ)*X 0 2+(434444261/1000000000 : ℝ)*X 1 0+(2085176699/5000000000 : ℝ)*X 1 1+(4525524729/10000000000 : ℝ)*X 1 2+(434444261/1000000000 : ℝ)*X 2 0+(2085176699/5000000000 : ℝ)*X 2 1+(4525524729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051651823/5000000000 : ℝ)*X 0 0+(2621442913/5000000000 : ℝ)*X 0 1+(5415584841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326403863/2500000000 : ℝ)*X 1 0+(-504663781/2500000000 : ℝ)*X 1 1+(5415584853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305615433/10000000000 : ℝ)*X 2 0+(2707792447/5000000000 : ℝ)*X 2 1+(-1009327547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543058633/1250000000 : ℝ)*X 0 0+(2262129493/5000000000 : ℝ)*X 0 1+(834325129/2000000000 : ℝ)*X 0 2+(543058633/1250000000 : ℝ)*X 1 0+(2262129493/5000000000 : ℝ)*X 1 1+(834325129/2000000000 : ℝ)*X 1 2+(543058633/1250000000 : ℝ)*X 2 0+(2262129493/5000000000 : ℝ)*X 2 1+(834325129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (637347147125287595876876637/57921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2125111517/100000000000000 : ℝ)*(base19) + (987564693/50000000000000 : ℝ)*(base23) + (80816131/100000000000000 : ℝ)*(lower2) + (278814039/100000000000000 : ℝ)*(upper3) + (267267/160000000000 : ℝ)*(upper5) + (267647300686143/6250000000000 : ℝ)*(major0) + (267647300686143/6250000000000 : ℝ)*(major1) + (267647300686143/6250000000000 : ℝ)*(major2) + (5749086130084013/100000000000000 : ℝ)*(sp0) + (287456306071473/5000000000000 : ℝ)*(sp1) + (5749126271411591/100000000000000 : ℝ)*(sp2) + (1407781293755653/50000000000000 : ℝ)*(sp3) + (10529114241/25000000000000 : ℝ)*(sp4) + (22421118767/100000000000000 : ℝ)*(sp7) + (2815585008630073/100000000000000 : ℝ)*(f.failure) + (5749128246540977/100000000000000 : ℝ)*(f.sum) + (936392065591/926750000000000000000000000 : ℝ)*base66 + (1484194654040228621/115843750000000000000000000000000 : ℝ)*base67 + (656077509687103621/115843750000000000000000000000000 : ℝ)*base69 + (64394589840021379/115843750000000000000000000000000 : ℝ)*base72 + (7261532044319/1853500000000000000000000000 : ℝ)*base73 + (1079870576401634871/115843750000000000000000000000000 : ℝ)*base75 + (185338750168771379/115843750000000000000000000000000 : ℝ)*base78 + (2287917863114728621/115843750000000000000000000000000 : ℝ)*base79 + (631812742309/741400000000000000000000000 : ℝ)*base82 + (7045461/1250000000000000000000 : ℝ)*base90 + (7045461/1250000000000000000000 : ℝ)*base92 + (7045461/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10342540889214335442963426441/926750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (398964709/20000000000000 : ℝ)*(base19) + (2125485901/100000000000000 : ℝ)*(base23) + (248777497/100000000000000 : ℝ)*(upper3) + (31011853/50000000000000 : ℝ)*(lower4) + (55693523/25000000000000 : ℝ)*(upper5) + (4313112908752401/100000000000000 : ℝ)*(major0) + (4313112908752401/100000000000000 : ℝ)*(major1) + (4313112908752401/100000000000000 : ℝ)*(major2) + (19405870249/50000000000000 : ℝ)*(sp1) + (8586105193/20000000000000 : ℝ)*(sp2) + (723802345813671/12500000000000 : ℝ)*(sp4) + (1447594489986331/25000000000000 : ℝ)*(sp5) + (2895186855248751/50000000000000 : ℝ)*(sp6) + (708951669748759/25000000000000 : ℝ)*(sp7) + (708951669748759/25000000000000 : ℝ)*(f.failure) + (723802345813671/12500000000000 : ℝ)*(f.sum) + (6090555042549/926750000000000000000000000 : ℝ)*base66 + (4794224958511857853/1853500000000000000000000000000000 : ℝ)*base68 + (3059677480265857853/1853500000000000000000000000000000 : ℝ)*base70 + (26966917014476857853/1853500000000000000000000000000000 : ℝ)*base72 + (9339998325231/1853500000000000000000000000 : ℝ)*base73 + (14508283846551142147/1853500000000000000000000000000000 : ℝ)*base75 + (1100485731917142147/1853500000000000000000000000000000 : ℝ)*base77 + (8368109461436857853/1853500000000000000000000000000000 : ℝ)*base80 + (4199982653469/1853500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2427837/312500000000000000000 : ℝ)*base89 + (2427837/312500000000000000000 : ℝ)*base91 + (2427837/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1275_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10981/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1275_s7_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103304921/10000000000 : ℝ)*x 0 + (541609149/1000000000 : ℝ)*x 1 + (1048474589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103304921/10000000000 : ℝ)^4235 ≤ (1279302386649/10000000000000 : ℝ)^3211 := by
    have hnat : (2103304921 : ℕ)^4235*10000000000000^3211 ≤ 1279302386649^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103304921 10000000000 1279302386649 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541609149/1000000000 : ℝ)^4235 ≤ (8908148473983/20000000000000 : ℝ)^3211 := by
    have hnat : (541609149 : ℕ)^4235*20000000000000^3211 ≤ 8908148473983^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541609149 1000000000 8908148473983 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048474589/2000000000 : ℝ)^4235 ≤ (42666233754479/100000000000000 : ℝ)^3211 := by
    have hnat : (1048474589 : ℕ)^4235*100000000000000^3211 ≤ 42666233754479^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048474589 2000000000 42666233754479 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103304921/10000000000 : ℝ), (541609149/1000000000 : ℝ), (1048474589/2000000000 : ℝ)] ![(1279302386649/10000000000000 : ℝ), (8908148473983/20000000000000 : ℝ), (42666233754479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103304921/10000000000 : ℝ)|^4235 ≤ (1279302386649/10000000000000 : ℝ)^3211
        have hw : |(-2103304921/10000000000 : ℝ)|=(2103304921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541609149/1000000000 : ℝ)|^4235 ≤ (8908148473983/20000000000000 : ℝ)^3211
        have hw : |(541609149/1000000000 : ℝ)|=(541609149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048474589/2000000000 : ℝ)|^4235 ≤ (42666233754479/100000000000000 : ℝ)^3211
        have hw : |(1048474589/2000000000 : ℝ)|=(1048474589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675011043/5000000000 : ℝ)*x 0 + (-1095936159/5000000000 : ℝ)*x 1 + (104847459/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675011043/5000000000 : ℝ)^4235 ≤ (21912763343937/50000000000000 : ℝ)^3211 := by
    have hnat : (2675011043 : ℕ)^4235*50000000000000^3211 ≤ 21912763343937^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675011043 5000000000 21912763343937 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095936159/5000000000 : ℝ)^4235 ≤ (13508239486987/100000000000000 : ℝ)^3211 := by
    have hnat : (1095936159 : ℕ)^4235*100000000000000^3211 ≤ 13508239486987^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095936159 5000000000 13508239486987 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104847459/200000000 : ℝ)^4235 ≤ (853324676163/2000000000000 : ℝ)^3211 := by
    have hnat : (104847459 : ℕ)^4235*2000000000000^3211 ≤ 853324676163^3211*200000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104847459 200000000 853324676163 2000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675011043/5000000000 : ℝ), (-1095936159/5000000000 : ℝ), (104847459/200000000 : ℝ)] ![(21912763343937/50000000000000 : ℝ), (13508239486987/100000000000000 : ℝ), (853324676163/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675011043/5000000000 : ℝ)|^4235 ≤ (21912763343937/50000000000000 : ℝ)^3211
        have hw : |(2675011043/5000000000 : ℝ)|=(2675011043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095936159/5000000000 : ℝ)|^4235 ≤ (13508239486987/100000000000000 : ℝ)^3211
        have hw : |(-1095936159/5000000000 : ℝ)|=(1095936159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104847459/200000000 : ℝ)|^4235 ≤ (853324676163/2000000000000 : ℝ)^3211
        have hw : |(104847459/200000000 : ℝ)|=(104847459/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350022187/10000000000 : ℝ)*x 0 + (2621186371/5000000000 : ℝ)*x 1 + (-2191872459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350022187/10000000000 : ℝ)^4235 ≤ (21912763889539/50000000000000 : ℝ)^3211 := by
    have hnat : (5350022187 : ℕ)^4235*50000000000000^3211 ≤ 21912763889539^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350022187 10000000000 21912763889539 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621186371/5000000000 : ℝ)^4235 ≤ (42666231575437/100000000000000 : ℝ)^3211 := by
    have hnat : (2621186371 : ℕ)^4235*100000000000000^3211 ≤ 42666231575437^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621186371 5000000000 42666231575437 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191872459/10000000000 : ℝ)^4235 ≤ (13508240633069/100000000000000 : ℝ)^3211 := by
    have hnat : (2191872459 : ℕ)^4235*100000000000000^3211 ≤ 13508240633069^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191872459 10000000000 13508240633069 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350022187/10000000000 : ℝ), (2621186371/5000000000 : ℝ), (-2191872459/10000000000 : ℝ)] ![(21912763889539/50000000000000 : ℝ), (42666231575437/100000000000000 : ℝ), (13508240633069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350022187/10000000000 : ℝ)|^4235 ≤ (21912763889539/50000000000000 : ℝ)^3211
        have hw : |(5350022187/10000000000 : ℝ)|=(5350022187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621186371/5000000000 : ℝ)|^4235 ≤ (42666231575437/100000000000000 : ℝ)^3211
        have hw : |(2621186371/5000000000 : ℝ)|=(2621186371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191872459/10000000000 : ℝ)|^4235 ≤ (13508240633069/100000000000000 : ℝ)^3211
        have hw : |(-2191872459/10000000000 : ℝ)|=(2191872459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2172225167/5000000000 : ℝ)*x 0 + (1042645149/2500000000 : ℝ)*x 1 + (1131323937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172225167/5000000000 : ℝ)^4235 ≤ (33302044113671/100000000000000 : ℝ)^3211 := by
    have hnat : (2172225167 : ℕ)^4235*100000000000000^3211 ≤ 33302044113671^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172225167 5000000000 33302044113671 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042645149/2500000000 : ℝ)^4235 ≤ (3155555019121/10000000000000 : ℝ)^3211 := by
    have hnat : (1042645149 : ℕ)^4235*10000000000000^3211 ≤ 3155555019121^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042645149 2500000000 3155555019121 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131323937/2500000000 : ℝ)^4235 ≤ (35142405676531/100000000000000 : ℝ)^3211 := by
    have hnat : (1131323937 : ℕ)^4235*100000000000000^3211 ≤ 35142405676531^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131323937 2500000000 35142405676531 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2172225167/5000000000 : ℝ), (1042645149/2500000000 : ℝ), (1131323937/2500000000 : ℝ)] ![(33302044113671/100000000000000 : ℝ), (3155555019121/10000000000000 : ℝ), (35142405676531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2172225167/5000000000 : ℝ)|^4235 ≤ (33302044113671/100000000000000 : ℝ)^3211
        have hw : |(2172225167/5000000000 : ℝ)|=(2172225167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042645149/2500000000 : ℝ)|^4235 ≤ (3155555019121/10000000000000 : ℝ)^3211
        have hw : |(1042645149/2500000000 : ℝ)|=(1042645149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131323937/2500000000 : ℝ)|^4235 ≤ (35142405676531/100000000000000 : ℝ)^3211
        have hw : |(1131323937/2500000000 : ℝ)|=(1131323937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051658729/5000000000 : ℝ)*x 0 + (1310747841/2500000000 : ℝ)*x 1 + (5415470171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051658729/5000000000 : ℝ)^4235 ≤ (12793124438729/100000000000000 : ℝ)^3211 := by
    have hnat : (1051658729 : ℕ)^4235*100000000000000^3211 ≤ 12793124438729^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051658729 5000000000 12793124438729 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310747841/2500000000 : ℝ)^4235 ≤ (42672872109833/100000000000000 : ℝ)^3211 := by
    have hnat : (1310747841 : ℕ)^4235*100000000000000^3211 ≤ 42672872109833^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310747841 2500000000 42672872109833 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415470171/10000000000 : ℝ)^4235 ≤ (44534003435051/100000000000000 : ℝ)^3211 := by
    have hnat : (5415470171 : ℕ)^4235*100000000000000^3211 ≤ 44534003435051^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415470171 10000000000 44534003435051 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051658729/5000000000 : ℝ), (1310747841/2500000000 : ℝ), (5415470171/10000000000 : ℝ)] ![(12793124438729/100000000000000 : ℝ), (42672872109833/100000000000000 : ℝ), (44534003435051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051658729/5000000000 : ℝ)|^4235 ≤ (12793124438729/100000000000000 : ℝ)^3211
        have hw : |(-1051658729/5000000000 : ℝ)|=(1051658729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310747841/2500000000 : ℝ)|^4235 ≤ (42672872109833/100000000000000 : ℝ)^3211
        have hw : |(1310747841/2500000000 : ℝ)|=(1310747841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415470171/10000000000 : ℝ)|^4235 ≤ (44534003435051/100000000000000 : ℝ)^3211
        have hw : |(5415470171/10000000000 : ℝ)|=(5415470171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265282141/500000000 : ℝ)*x 0 + (-2018775219/10000000000 : ℝ)*x 1 + (676933749/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265282141/500000000 : ℝ)^4235 ≤ (8669337674497/20000000000000 : ℝ)^3211 := by
    have hnat : (265282141 : ℕ)^4235*20000000000000^3211 ≤ 8669337674497^3211*500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265282141 500000000 8669337674497 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018775219/10000000000 : ℝ)^4235 ≤ (12119310111141/100000000000000 : ℝ)^3211 := by
    have hnat : (2018775219 : ℕ)^4235*100000000000000^3211 ≤ 12119310111141^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018775219 10000000000 12119310111141 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676933749/1250000000 : ℝ)^4235 ≤ (22267000746811/50000000000000 : ℝ)^3211 := by
    have hnat : (676933749 : ℕ)^4235*50000000000000^3211 ≤ 22267000746811^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676933749 1250000000 22267000746811 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265282141/500000000 : ℝ), (-2018775219/10000000000 : ℝ), (676933749/1250000000 : ℝ)] ![(8669337674497/20000000000000 : ℝ), (12119310111141/100000000000000 : ℝ), (22267000746811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265282141/500000000 : ℝ)|^4235 ≤ (8669337674497/20000000000000 : ℝ)^3211
        have hw : |(265282141/500000000 : ℝ)|=(265282141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2018775219/10000000000 : ℝ)|^4235 ≤ (12119310111141/100000000000000 : ℝ)^3211
        have hw : |(-2018775219/10000000000 : ℝ)|=(2018775219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676933749/1250000000 : ℝ)|^4235 ≤ (22267000746811/50000000000000 : ℝ)^3211
        have hw : |(676933749/1250000000 : ℝ)|=(676933749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663205367/1250000000 : ℝ)*x 0 + (1083094011/2000000000 : ℝ)*x 1 + (-31543359/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663205367/1250000000 : ℝ)^4235 ≤ (5418336202803/12500000000000 : ℝ)^3211 := by
    have hnat : (663205367 : ℕ)^4235*12500000000000^3211 ≤ 5418336202803^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663205367 1250000000 5418336202803 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083094011/2000000000 : ℝ)^4235 ≤ (22267001088459/50000000000000 : ℝ)^3211 := by
    have hnat : (1083094011 : ℕ)^4235*50000000000000^3211 ≤ 22267001088459^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083094011 2000000000 22267001088459 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31543359/156250000 : ℝ)^4235 ≤ (6059654093561/50000000000000 : ℝ)^3211 := by
    have hnat : (31543359 : ℕ)^4235*50000000000000^3211 ≤ 6059654093561^3211*156250000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31543359 156250000 6059654093561 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663205367/1250000000 : ℝ), (1083094011/2000000000 : ℝ), (-31543359/156250000 : ℝ)] ![(5418336202803/12500000000000 : ℝ), (22267001088459/50000000000000 : ℝ), (6059654093561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663205367/1250000000 : ℝ)|^4235 ≤ (5418336202803/12500000000000 : ℝ)^3211
        have hw : |(663205367/1250000000 : ℝ)|=(663205367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083094011/2000000000 : ℝ)|^4235 ≤ (22267001088459/50000000000000 : ℝ)^3211
        have hw : |(1083094011/2000000000 : ℝ)|=(1083094011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31543359/156250000 : ℝ)|^4235 ≤ (6059654093561/50000000000000 : ℝ)^3211
        have hw : |(-31543359/156250000 : ℝ)|=(31543359/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_s7_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434447663/1000000000 : ℝ)*x 0 + (4524033533/10000000000 : ℝ)*x 1 + (208592467/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434447663/1000000000 : ℝ)^4235 ≤ (33302309965269/100000000000000 : ℝ)^3211 := by
    have hnat : (434447663 : ℕ)^4235*100000000000000^3211 ≤ 33302309965269^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434447663 1000000000 33302309965269 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524033533/10000000000 : ℝ)^4235 ≤ (8782369565691/25000000000000 : ℝ)^3211 := by
    have hnat : (4524033533 : ℕ)^4235*25000000000000^3211 ≤ 8782369565691^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524033533 10000000000 8782369565691 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208592467/500000000 : ℝ)^4235 ≤ (31568211756929/100000000000000 : ℝ)^3211 := by
    have hnat : (208592467 : ℕ)^4235*100000000000000^3211 ≤ 31568211756929^3211*500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208592467 500000000 31568211756929 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434447663/1000000000 : ℝ), (4524033533/10000000000 : ℝ), (208592467/500000000 : ℝ)] ![(33302309965269/100000000000000 : ℝ), (8782369565691/25000000000000 : ℝ), (31568211756929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434447663/1000000000 : ℝ)|^4235 ≤ (33302309965269/100000000000000 : ℝ)^3211
        have hw : |(434447663/1000000000 : ℝ)|=(434447663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524033533/10000000000 : ℝ)|^4235 ≤ (8782369565691/25000000000000 : ℝ)^3211
        have hw : |(4524033533/10000000000 : ℝ)|=(4524033533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208592467/500000000 : ℝ)|^4235 ≤ (31568211756929/100000000000000 : ℝ)^3211
        have hw : |(208592467/500000000 : ℝ)|=(208592467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10981/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1373/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (733/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10981/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10981/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10981/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10981/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10981/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10981/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10981/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (10796402599485113/100000000000000000000 : ℝ) := by
    have hpowers : (10981/100000 : ℝ)^2117 ≤ (10796402599485113/100000000000000000000 : ℝ)^512 := by
      have hnat : (10981 : ℕ)^2117*100000000000000000000^512 ≤ 10796402599485113^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10981 100000 10796402599485113 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10981/100000 : ℝ)) (X := (10796402599485113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14663/100000 : ℝ) ^ (2117/512 : ℝ) ≤ (35688380244308237/100000000000000000000 : ℝ) := by
    have hpowers : (14663/100000 : ℝ)^2117 ≤ (35688380244308237/100000000000000000000 : ℝ)^512 := by
      have hnat : (14663 : ℕ)^2117*100000000000000000000^512 ≤ 35688380244308237^512*100000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14663 100000 35688380244308237 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14663/100000 : ℝ)) (X := (35688380244308237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010796402599485113/50000000000000000000 : ℝ) ≤ (5000261091437223/5000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50010796402599485113/50000000000000000000 : ℝ)^512 ≤ (5000261091437223/5000000000000000 : ℝ)^2117 := by
      have hnat : (50010796402599485113 : ℕ)^512*5000000000000000^2117 ≤ 5000261091437223^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010796402599485113 50000000000000000000 5000261091437223 5000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000261091437223/5000000000000000 : ℝ)) (X := (50010796402599485113/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000929695656875867/2000000000000000000 : ℝ) ≤ (10001124044217313/10000000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (2000929695656875867/2000000000000000000 : ℝ)^512 ≤ (10001124044217313/10000000000000000 : ℝ)^2117 := by
      have hnat : (2000929695656875867 : ℕ)^512*10000000000000000^2117 ≤ 10001124044217313^2117*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000929695656875867 2000000000000000000 10001124044217313 10000000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001124044217313/10000000000000000 : ℝ)) (X := (2000929695656875867/2000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035688380244308237/50000000000000000000 : ℝ) ≤ (500086295278009/500000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50035688380244308237/50000000000000000000 : ℝ)^512 ≤ (500086295278009/500000000000000 : ℝ)^2117 := by
      have hnat : (50035688380244308237 : ℕ)^512*500000000000000^2117 ≤ 500086295278009^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035688380244308237 50000000000000000000 500086295278009 500000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500086295278009/500000000000000 : ℝ)) (X := (50035688380244308237/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10796402599485113/100000000000000000000 : ℝ) ≤ ((18404352299265832559/18410000000000000000 : ℝ)+2*(601861342867/368200000000000 : ℝ)*(10981/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (18404352299265832559/18410000000000000000 : ℝ)+2*(601861342867/368200000000000 : ℝ)*(10981/100000 : ℝ)=(5000261091437223/5000000000000000 : ℝ) by norm_num, show 1+2*(10796402599485113/100000000000000000000 : ℝ)=(50010796402599485113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35688380244308237/100000000000000000000 : ℝ)+(10796402599485113/100000000000000000000 : ℝ) ≤ ((18404352299265832559/18410000000000000000 : ℝ)+(601861342867/368200000000000 : ℝ)*((14663/100000 : ℝ)+(10981/100000 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (18404352299265832559/18410000000000000000 : ℝ)+(601861342867/368200000000000 : ℝ)*((14663/100000 : ℝ)+(10981/100000 : ℝ))=(10001124044217313/10000000000000000 : ℝ) by norm_num, show 1+(35688380244308237/100000000000000000000 : ℝ)+(10796402599485113/100000000000000000000 : ℝ)=(2000929695656875867/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35688380244308237/100000000000000000000 : ℝ) ≤ ((18404352299265832559/18410000000000000000 : ℝ)+2*(601861342867/368200000000000 : ℝ)*(14663/100000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (18404352299265832559/18410000000000000000 : ℝ)+2*(601861342867/368200000000000 : ℝ)*(14663/100000 : ℝ)=(500086295278009/500000000000000 : ℝ) by norm_num, show 1+2*(35688380244308237/100000000000000000000 : ℝ)=(50035688380244308237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18404352299265832559/18410000000000000000 : ℝ)*(X 1 0+X 2 0)+(601861342867/368200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10981/100000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (18404352299265832559/18410000000000000000 : ℝ)) (alpha := (601861342867/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18404352299265832559/18410000000000000000 : ℝ)*(X 0 1+X 2 1)+(601861342867/368200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10981/100000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (18404352299265832559/18410000000000000000 : ℝ)) (alpha := (601861342867/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18404352299265832559/18410000000000000000 : ℝ)*(X 0 2+X 1 2)+(601861342867/368200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (10981/100000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (18404352299265832559/18410000000000000000 : ℝ)) (alpha := (601861342867/368200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2103304921/10000000000 : ℝ)*X 0 0+(541609149/1000000000 : ℝ)*X 0 1+(1048474589/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675011043/5000000000 : ℝ)*X 1 0+(-1095936159/5000000000 : ℝ)*X 1 1+(104847459/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350022187/10000000000 : ℝ)*X 2 0+(2621186371/5000000000 : ℝ)*X 2 1+(-2191872459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2172225167/5000000000 : ℝ)*X 0 0+(1042645149/2500000000 : ℝ)*X 0 1+(1131323937/2500000000 : ℝ)*X 0 2+(2172225167/5000000000 : ℝ)*X 1 0+(1042645149/2500000000 : ℝ)*X 1 1+(1131323937/2500000000 : ℝ)*X 1 2+(2172225167/5000000000 : ℝ)*X 2 0+(1042645149/2500000000 : ℝ)*X 2 1+(1131323937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051658729/5000000000 : ℝ)*X 0 0+(1310747841/2500000000 : ℝ)*X 0 1+(5415470171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265282141/500000000 : ℝ)*X 1 0+(-2018775219/10000000000 : ℝ)*X 1 1+(676933749/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663205367/1250000000 : ℝ)*X 2 0+(1083094011/2000000000 : ℝ)*X 2 1+(-31543359/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434447663/1000000000 : ℝ)*X 0 0+(4524033533/10000000000 : ℝ)*X 0 1+(208592467/500000000 : ℝ)*X 0 2+(434447663/1000000000 : ℝ)*X 1 0+(4524033533/10000000000 : ℝ)*X 1 1+(208592467/500000000 : ℝ)*X 1 2+(434447663/1000000000 : ℝ)*X 2 0+(4524033533/10000000000 : ℝ)*X 2 1+(208592467/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (299703234839710127684363097/57531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60296227/12500000000000 : ℝ)*(base19) + (606424403/100000000000000 : ℝ)*(base23) + (4718217/50000000000000 : ℝ)*(upper2) + (124981553/100000000000000 : ℝ)*(upper3) + (535976688723711/12500000000000 : ℝ)*(major0) + (535976688723711/12500000000000 : ℝ)*(major1) + (535976688723711/12500000000000 : ℝ)*(major2) + (5756447936100587/100000000000000 : ℝ)*(sp0) + (5756453657772581/100000000000000 : ℝ)*(sp1) + (1439113315428353/25000000000000 : ℝ)*(sp2) + (2819167002008883/100000000000000 : ℝ)*(sp3) + (620404181/10000000000000 : ℝ)*(sp4) + (272004581/100000000000000 : ℝ)*(sp6) + (356486341/6250000000000 : ℝ)*(sp7) + (2819172705790339/100000000000000 : ℝ)*(f.failure) + (5756454140142397/100000000000000 : ℝ)*(f.sum) + (29215151190773/9205000000000000000000000000 : ℝ)*base65 + (1529073836742293551/230125000000000000000000000000000 : ℝ)*base68 + (2326849316352668551/230125000000000000000000000000000 : ℝ)*base70 + (1489120082400043551/230125000000000000000000000000000 : ℝ)*base72 + (9127530541821/4602500000000000000000000000 : ℝ)*base74 + (1891180285068293551/230125000000000000000000000000000 : ℝ)*base76 + (1871711615256793551/230125000000000000000000000000000 : ℝ)*base78 + (368697036764081449/230125000000000000000000000000000 : ℝ)*base79 + (12729515712763/2301250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15984777/1250000000000000000000 : ℝ)*base89 + (15984777/1250000000000000000000 : ℝ)*base91 + (15984777/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (825683238539101389151258143/115062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288156013/100000000000000 : ℝ)*(base19) + (471025403/50000000000000 : ℝ)*(base23) + (1416261/5000000000000 : ℝ)*(lower1) + (100925087/50000000000000 : ℝ)*(lower4) + (22570373/100000000000000 : ℝ)*(lower5) + (539827188579841/12500000000000 : ℝ)*(major0) + (539827188579841/12500000000000 : ℝ)*(major1) + (539827188579841/12500000000000 : ℝ)*(major2) + (17537131281/100000000000000 : ℝ)*(sp2) + (360162811/20000000000000 : ℝ)*(sp3) + (724726113461179/12500000000000 : ℝ)*(sp4) + (5797808619533419/100000000000000 : ℝ)*(sp5) + (1159558085701469/20000000000000 : ℝ)*(sp6) + (113576962783019/4000000000000 : ℝ)*(sp7) + (283942587038953/10000000000000 : ℝ)*(f.failure) + (724726113461179/12500000000000 : ℝ)*(f.sum) + (3032717800129/1150625000000000000000000000 : ℝ)*base66 + (1935839158924181881/230125000000000000000000000000000 : ℝ)*base68 + (956924760282806881/230125000000000000000000000000000 : ℝ)*base70 + (1678699698016193119/230125000000000000000000000000000 : ℝ)*base71 + (3083950644591/4602500000000000000000000000 : ℝ)*base74 + (23411533925015193119/230125000000000000000000000000000 : ℝ)*base75 + (1347850162145318119/230125000000000000000000000000000 : ℝ)*base77 + (4872424792002193119/230125000000000000000000000000000 : ℝ)*base79 + (29526967210317/9205000000000000000000000000 : ℝ)*base82 + (679621/125000000000000000000 : ℝ)*base90 + (679621/125000000000000000000 : ℝ)*base92 + (679621/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1275_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10981/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (733/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1275_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1275_box_0 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930509539/10000000000 : ℝ)*x 0 + (5392711207/10000000000 : ℝ)*x 1 + (1348177441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930509539/10000000000 : ℝ)^4235 ≤ (11425364011261/100000000000000 : ℝ)^3211 := by
    have hnat : (1930509539 : ℕ)^4235*100000000000000^3211 ≤ 11425364011261^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930509539 10000000000 11425364011261 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392711207/10000000000 : ℝ)^4235 ≤ (8857465160999/20000000000000 : ℝ)^3211 := by
    have hnat : (5392711207 : ℕ)^4235*20000000000000^3211 ≤ 8857465160999^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392711207 10000000000 8857465160999 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348177441/2500000000 : ℝ)^4235 ≤ (5535913771907/12500000000000 : ℝ)^3211 := by
    have hnat : (1348177441 : ℕ)^4235*12500000000000^3211 ≤ 5535913771907^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348177441 2500000000 5535913771907 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930509539/10000000000 : ℝ), (5392711207/10000000000 : ℝ), (1348177441/2500000000 : ℝ)] ![(11425364011261/100000000000000 : ℝ), (8857465160999/20000000000000 : ℝ), (5535913771907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930509539/10000000000 : ℝ)|^4235 ≤ (11425364011261/100000000000000 : ℝ)^3211
        have hw : |(-1930509539/10000000000 : ℝ)|=(1930509539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392711207/10000000000 : ℝ)|^4235 ≤ (8857465160999/20000000000000 : ℝ)^3211
        have hw : |(5392711207/10000000000 : ℝ)|=(5392711207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348177441/2500000000 : ℝ)|^4235 ≤ (5535913771907/12500000000000 : ℝ)^3211
        have hw : |(1348177441/2500000000 : ℝ)|=(1348177441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_1 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284045753/10000000000 : ℝ)*x 0 + (-2079018079/10000000000 : ℝ)*x 1 + (5392710887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284045753/10000000000 : ℝ)^4235 ≤ (43114123797717/100000000000000 : ℝ)^3211 := by
    have hnat : (5284045753 : ℕ)^4235*100000000000000^3211 ≤ 43114123797717^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284045753 10000000000 43114123797717 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079018079/10000000000 : ℝ)^4235 ≤ (1574819230581/12500000000000 : ℝ)^3211 := by
    have hnat : (2079018079 : ℕ)^4235*12500000000000^3211 ≤ 1574819230581^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079018079 10000000000 1574819230581 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392710887/10000000000 : ℝ)^4235 ≤ (2214366116947/5000000000000 : ℝ)^3211 := by
    have hnat : (5392710887 : ℕ)^4235*5000000000000^3211 ≤ 2214366116947^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392710887 10000000000 2214366116947 5000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284045753/10000000000 : ℝ), (-2079018079/10000000000 : ℝ), (5392710887/10000000000 : ℝ)] ![(43114123797717/100000000000000 : ℝ), (1574819230581/12500000000000 : ℝ), (2214366116947/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284045753/10000000000 : ℝ)|^4235 ≤ (43114123797717/100000000000000 : ℝ)^3211
        have hw : |(5284045753/10000000000 : ℝ)|=(5284045753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079018079/10000000000 : ℝ)|^4235 ≤ (1574819230581/12500000000000 : ℝ)^3211
        have hw : |(-2079018079/10000000000 : ℝ)|=(2079018079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392710887/10000000000 : ℝ)|^4235 ≤ (2214366116947/5000000000000 : ℝ)^3211
        have hw : |(5392710887/10000000000 : ℝ)|=(5392710887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_2 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321011619/2500000000 : ℝ)*x 0 + (337044439/625000000 : ℝ)*x 1 + (-51975423/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321011619/2500000000 : ℝ)^4235 ≤ (43114131578161/100000000000000 : ℝ)^3211 := by
    have hnat : (1321011619 : ℕ)^4235*100000000000000^3211 ≤ 43114131578161^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321011619 2500000000 43114131578161 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337044439/625000000 : ℝ)^4235 ≤ (8857464764569/20000000000000 : ℝ)^3211 := by
    have hnat : (337044439 : ℕ)^4235*20000000000000^3211 ≤ 8857464764569^3211*625000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337044439 625000000 8857464764569 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51975423/250000000 : ℝ)^4235 ≤ (12598544581493/100000000000000 : ℝ)^3211 := by
    have hnat : (51975423 : ℕ)^4235*100000000000000^3211 ≤ 12598544581493^3211*250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51975423 250000000 12598544581493 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321011619/2500000000 : ℝ), (337044439/625000000 : ℝ), (-51975423/250000000 : ℝ)] ![(43114131578161/100000000000000 : ℝ), (8857464764569/20000000000000 : ℝ), (12598544581493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321011619/2500000000 : ℝ)|^4235 ≤ (43114131578161/100000000000000 : ℝ)^3211
        have hw : |(1321011619/2500000000 : ℝ)|=(1321011619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337044439/625000000 : ℝ)|^4235 ≤ (8857464764569/20000000000000 : ℝ)^3211
        have hw : |(337044439/625000000 : ℝ)|=(337044439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51975423/250000000 : ℝ)|^4235 ≤ (12598544581493/100000000000000 : ℝ)^3211
        have hw : |(-51975423/250000000 : ℝ)|=(51975423/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_3 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1123581881/2500000000 : ℝ)*x 0 + (2136779741/5000000000 : ℝ)*x 1 + (1068390079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123581881/2500000000 : ℝ)^4235 ≤ (17412783192009/50000000000000 : ℝ)^3211 := by
    have hnat : (1123581881 : ℕ)^4235*50000000000000^3211 ≤ 17412783192009^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123581881 2500000000 17412783192009 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136779741/5000000000 : ℝ)^4235 ≤ (32587212608529/100000000000000 : ℝ)^3211 := by
    have hnat : (2136779741 : ℕ)^4235*100000000000000^3211 ≤ 32587212608529^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136779741 5000000000 32587212608529 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068390079/2500000000 : ℝ)^4235 ≤ (8146805249027/25000000000000 : ℝ)^3211 := by
    have hnat : (1068390079 : ℕ)^4235*25000000000000^3211 ≤ 8146805249027^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068390079 2500000000 8146805249027 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123581881/2500000000 : ℝ), (2136779741/5000000000 : ℝ), (1068390079/2500000000 : ℝ)] ![(17412783192009/50000000000000 : ℝ), (32587212608529/100000000000000 : ℝ), (8146805249027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123581881/2500000000 : ℝ)|^4235 ≤ (17412783192009/50000000000000 : ℝ)^3211
        have hw : |(1123581881/2500000000 : ℝ)|=(1123581881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2136779741/5000000000 : ℝ)|^4235 ≤ (32587212608529/100000000000000 : ℝ)^3211
        have hw : |(2136779741/5000000000 : ℝ)|=(2136779741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1068390079/2500000000 : ℝ)|^4235 ≤ (8146805249027/25000000000000 : ℝ)^3211
        have hw : |(1068390079/2500000000 : ℝ)|=(1068390079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_4 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2278866287/10000000000 : ℝ)*x 0 + (2631608029/5000000000 : ℝ)*x 1 + (2631607943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2278866287/10000000000 : ℝ)^4235 ≤ (2843956558053/20000000000000 : ℝ)^3211 := by
    have hnat : (2278866287 : ℕ)^4235*20000000000000^3211 ≤ 2843956558053^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278866287 10000000000 2843956558053 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631608029/5000000000 : ℝ)^4235 ≤ (1715604380691/4000000000000 : ℝ)^3211 := by
    have hnat : (2631608029 : ℕ)^4235*4000000000000^3211 ≤ 1715604380691^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631608029 5000000000 1715604380691 4000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631607943/5000000000 : ℝ)^4235 ≤ (2680631729291/6250000000000 : ℝ)^3211 := by
    have hnat : (2631607943 : ℕ)^4235*6250000000000^3211 ≤ 2680631729291^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631607943 5000000000 2680631729291 6250000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2278866287/10000000000 : ℝ), (2631608029/5000000000 : ℝ), (2631607943/5000000000 : ℝ)] ![(2843956558053/20000000000000 : ℝ), (1715604380691/4000000000000 : ℝ), (2680631729291/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2278866287/10000000000 : ℝ)|^4235 ≤ (2843956558053/20000000000000 : ℝ)^3211
        have hw : |(-2278866287/10000000000 : ℝ)|=(2278866287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631608029/5000000000 : ℝ)|^4235 ≤ (1715604380691/4000000000000 : ℝ)^3211
        have hw : |(2631608029/5000000000 : ℝ)|=(2631608029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631607943/5000000000 : ℝ)|^4235 ≤ (2680631729291/6250000000000 : ℝ)^3211
        have hw : |(2631607943/5000000000 : ℝ)|=(2631607943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_5 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215010497/400000000 : ℝ)*x 0 + (-213047897/1000000000 : ℝ)*x 1 + (5263216021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215010497/400000000 : ℝ)^4235 ≤ (22049214147549/50000000000000 : ℝ)^3211 := by
    have hnat : (215010497 : ℕ)^4235*50000000000000^3211 ≤ 22049214147549^3211*400000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215010497 400000000 22049214147549 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213047897/1000000000 : ℝ)^4235 ≤ (13011462568399/100000000000000 : ℝ)^3211 := by
    have hnat : (213047897 : ℕ)^4235*100000000000000^3211 ≤ 13011462568399^3211*1000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213047897 1000000000 13011462568399 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263216021/10000000000 : ℝ)^4235 ≤ (42890109119607/100000000000000 : ℝ)^3211 := by
    have hnat : (5263216021 : ℕ)^4235*100000000000000^3211 ≤ 42890109119607^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263216021 10000000000 42890109119607 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215010497/400000000 : ℝ), (-213047897/1000000000 : ℝ), (5263216021/10000000000 : ℝ)] ![(22049214147549/50000000000000 : ℝ), (13011462568399/100000000000000 : ℝ), (42890109119607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215010497/400000000 : ℝ)|^4235 ≤ (22049214147549/50000000000000 : ℝ)^3211
        have hw : |(215010497/400000000 : ℝ)|=(215010497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213047897/1000000000 : ℝ)|^4235 ≤ (13011462568399/100000000000000 : ℝ)^3211
        have hw : |(-213047897/1000000000 : ℝ)|=(213047897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263216021/10000000000 : ℝ)|^4235 ≤ (42890109119607/100000000000000 : ℝ)^3211
        have hw : |(5263216021/10000000000 : ℝ)|=(5263216021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_6 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075052443/2000000000 : ℝ)*x 0 + (2631608091/5000000000 : ℝ)*x 1 + (-1065239519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075052443/2000000000 : ℝ)^4235 ≤ (44098426022849/100000000000000 : ℝ)^3211 := by
    have hnat : (1075052443 : ℕ)^4235*100000000000000^3211 ≤ 44098426022849^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075052443 2000000000 44098426022849 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631608091/5000000000 : ℝ)^4235 ≤ (42890110850001/100000000000000 : ℝ)^3211 := by
    have hnat : (2631608091 : ℕ)^4235*100000000000000^3211 ≤ 42890110850001^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631608091 5000000000 42890110850001 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065239519/5000000000 : ℝ)^4235 ≤ (6505731558067/50000000000000 : ℝ)^3211 := by
    have hnat : (1065239519 : ℕ)^4235*50000000000000^3211 ≤ 6505731558067^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065239519 5000000000 6505731558067 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075052443/2000000000 : ℝ), (2631608091/5000000000 : ℝ), (-1065239519/5000000000 : ℝ)] ![(44098426022849/100000000000000 : ℝ), (42890110850001/100000000000000 : ℝ), (6505731558067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075052443/2000000000 : ℝ)|^4235 ≤ (44098426022849/100000000000000 : ℝ)^3211
        have hw : |(1075052443/2000000000 : ℝ)|=(1075052443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631608091/5000000000 : ℝ)|^4235 ≤ (42890110850001/100000000000000 : ℝ)^3211
        have hw : |(2631608091/5000000000 : ℝ)|=(2631608091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065239519/5000000000 : ℝ)|^4235 ≤ (6505731558067/50000000000000 : ℝ)^3211
        have hw : |(-1065239519/5000000000 : ℝ)|=(1065239519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_7 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193750589/10000000000 : ℝ)*x 0 + (884758457/2000000000 : ℝ)*x 1 + (4423792421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193750589/10000000000 : ℝ)^4235 ≤ (317869709509/1000000000000 : ℝ)^3211 := by
    have hnat : (4193750589 : ℕ)^4235*1000000000000^3211 ≤ 317869709509^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193750589 10000000000 317869709509 1000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884758457/2000000000 : ℝ)^4235 ≤ (34106513824313/100000000000000 : ℝ)^3211 := by
    have hnat : (884758457 : ℕ)^4235*100000000000000^3211 ≤ 34106513824313^3211*2000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884758457 2000000000 34106513824313 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4423792421/10000000000 : ℝ)^4235 ≤ (1364260608289/4000000000000 : ℝ)^3211 := by
    have hnat : (4423792421 : ℕ)^4235*4000000000000^3211 ≤ 1364260608289^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423792421 10000000000 1364260608289 4000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193750589/10000000000 : ℝ), (884758457/2000000000 : ℝ), (4423792421/10000000000 : ℝ)] ![(317869709509/1000000000000 : ℝ), (34106513824313/100000000000000 : ℝ), (1364260608289/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193750589/10000000000 : ℝ)|^4235 ≤ (317869709509/1000000000000 : ℝ)^3211
        have hw : |(4193750589/10000000000 : ℝ)|=(4193750589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884758457/2000000000 : ℝ)|^4235 ≤ (34106513824313/100000000000000 : ℝ)^3211
        have hw : |(884758457/2000000000 : ℝ)|=(884758457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4423792421/10000000000 : ℝ)|^4235 ≤ (1364260608289/4000000000000 : ℝ)^3211
        have hw : |(4423792421/10000000000 : ℝ)|=(4423792421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_8 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205905951/10000000000 : ℝ)*x 0 + (2587198749/5000000000 : ℝ)*x 1 + (5406753821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205905951/10000000000 : ℝ)^4235 ≤ (13622424532181/100000000000000 : ℝ)^3211 := by
    have hnat : (2205905951 : ℕ)^4235*100000000000000^3211 ≤ 13622424532181^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205905951 10000000000 13622424532181 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587198749/5000000000 : ℝ)^4235 ≤ (20969042540933/50000000000000 : ℝ)^3211 := by
    have hnat : (2587198749 : ℕ)^4235*50000000000000^3211 ≤ 20969042540933^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587198749 5000000000 20969042540933 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406753821/10000000000 : ℝ)^4235 ≤ (22219745187263/50000000000000 : ℝ)^3211 := by
    have hnat : (5406753821 : ℕ)^4235*50000000000000^3211 ≤ 22219745187263^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406753821 10000000000 22219745187263 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205905951/10000000000 : ℝ), (2587198749/5000000000 : ℝ), (5406753821/10000000000 : ℝ)] ![(13622424532181/100000000000000 : ℝ), (20969042540933/50000000000000 : ℝ), (22219745187263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205905951/10000000000 : ℝ)|^4235 ≤ (13622424532181/100000000000000 : ℝ)^3211
        have hw : |(-2205905951/10000000000 : ℝ)|=(2205905951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587198749/5000000000 : ℝ)|^4235 ≤ (20969042540933/50000000000000 : ℝ)^3211
        have hw : |(2587198749/5000000000 : ℝ)|=(2587198749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406753821/10000000000 : ℝ)|^4235 ≤ (22219745187263/50000000000000 : ℝ)^3211
        have hw : |(5406753821/10000000000 : ℝ)|=(5406753821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_9 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274147889/10000000000 : ℝ)*x 0 + (-2073299961/10000000000 : ℝ)*x 1 + (5406753417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274147889/10000000000 : ℝ)^4235 ≤ (21503820703029/50000000000000 : ℝ)^3211 := by
    have hnat : (5274147889 : ℕ)^4235*50000000000000^3211 ≤ 21503820703029^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274147889 10000000000 21503820703029 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073299961/10000000000 : ℝ)^4235 ≤ (12552872589331/100000000000000 : ℝ)^3211 := by
    have hnat : (2073299961 : ℕ)^4235*100000000000000^3211 ≤ 12552872589331^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073299961 10000000000 12552872589331 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406753417/10000000000 : ℝ)^4235 ≤ (22219742997501/50000000000000 : ℝ)^3211 := by
    have hnat : (5406753417 : ℕ)^4235*50000000000000^3211 ≤ 22219742997501^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406753417 10000000000 22219742997501 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274147889/10000000000 : ℝ), (-2073299961/10000000000 : ℝ), (5406753417/10000000000 : ℝ)] ![(21503820703029/50000000000000 : ℝ), (12552872589331/100000000000000 : ℝ), (22219742997501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274147889/10000000000 : ℝ)|^4235 ≤ (21503820703029/50000000000000 : ℝ)^3211
        have hw : |(5274147889/10000000000 : ℝ)|=(5274147889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073299961/10000000000 : ℝ)|^4235 ≤ (12552872589331/100000000000000 : ℝ)^3211
        have hw : |(-2073299961/10000000000 : ℝ)|=(2073299961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406753417/10000000000 : ℝ)|^4235 ≤ (22219742997501/50000000000000 : ℝ)^3211
        have hw : |(5406753417/10000000000 : ℝ)|=(5406753417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_10 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210965927/400000000 : ℝ)*x 0 + (5406753097/10000000000 : ℝ)*x 1 + (-2073300009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210965927/400000000 : ℝ)^4235 ≤ (1075191112049/2500000000000 : ℝ)^3211 := by
    have hnat : (210965927 : ℕ)^4235*2500000000000^3211 ≤ 1075191112049^3211*400000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210965927 400000000 1075191112049 2500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406753097/10000000000 : ℝ)^4235 ≤ (44439482526071/100000000000000 : ℝ)^3211 := by
    have hnat : (5406753097 : ℕ)^4235*100000000000000^3211 ≤ 44439482526071^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406753097 10000000000 44439482526071 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073300009/10000000000 : ℝ)^4235 ≤ (3138218243157/25000000000000 : ℝ)^3211 := by
    have hnat : (2073300009 : ℕ)^4235*25000000000000^3211 ≤ 3138218243157^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073300009 10000000000 3138218243157 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210965927/400000000 : ℝ), (5406753097/10000000000 : ℝ), (-2073300009/10000000000 : ℝ)] ![(1075191112049/2500000000000 : ℝ), (44439482526071/100000000000000 : ℝ), (3138218243157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210965927/400000000 : ℝ)|^4235 ≤ (1075191112049/2500000000000 : ℝ)^3211
        have hw : |(210965927/400000000 : ℝ)|=(210965927/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406753097/10000000000 : ℝ)|^4235 ≤ (44439482526071/100000000000000 : ℝ)^3211
        have hw : |(5406753097/10000000000 : ℝ)|=(5406753097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073300009/10000000000 : ℝ)|^4235 ≤ (3138218243157/25000000000000 : ℝ)^3211
        have hw : |(-2073300009/10000000000 : ℝ)|=(2073300009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_11 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4526363567/10000000000 : ℝ)*x 0 + (4257254023/10000000000 : ℝ)*x 1 + (1064313547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4526363567/10000000000 : ℝ)^4235 ≤ (8788335753503/25000000000000 : ℝ)^3211 := by
    have hnat : (4526363567 : ℕ)^4235*25000000000000^3211 ≤ 8788335753503^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526363567 10000000000 8788335753503 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4257254023/10000000000 : ℝ)^4235 ≤ (4052915957259/12500000000000 : ℝ)^3211 := by
    have hnat : (4257254023 : ℕ)^4235*12500000000000^3211 ≤ 4052915957259^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257254023 10000000000 4052915957259 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064313547/2500000000 : ℝ)^4235 ≤ (32423329315463/100000000000000 : ℝ)^3211 := by
    have hnat : (1064313547 : ℕ)^4235*100000000000000^3211 ≤ 32423329315463^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064313547 2500000000 32423329315463 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4526363567/10000000000 : ℝ), (4257254023/10000000000 : ℝ), (1064313547/2500000000 : ℝ)] ![(8788335753503/25000000000000 : ℝ), (4052915957259/12500000000000 : ℝ), (32423329315463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4526363567/10000000000 : ℝ)|^4235 ≤ (8788335753503/25000000000000 : ℝ)^3211
        have hw : |(4526363567/10000000000 : ℝ)|=(4526363567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4257254023/10000000000 : ℝ)|^4235 ≤ (4052915957259/12500000000000 : ℝ)^3211
        have hw : |(4257254023/10000000000 : ℝ)|=(4257254023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1064313547/2500000000 : ℝ)|^4235 ≤ (32423329315463/100000000000000 : ℝ)^3211
        have hw : |(1064313547/2500000000 : ℝ)|=(1064313547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_12 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001972893/5000000000 : ℝ)*x 0 + (5479162373/10000000000 : ℝ)*x 1 + (5252210963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001972893/5000000000 : ℝ)^4235 ≤ (2400406357387/20000000000000 : ℝ)^3211 := by
    have hnat : (1001972893 : ℕ)^4235*20000000000000^3211 ≤ 2400406357387^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001972893 5000000000 2400406357387 20000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479162373/10000000000 : ℝ)^4235 ≤ (45226099643061/100000000000000 : ℝ)^3211 := by
    have hnat : (5479162373 : ℕ)^4235*100000000000000^3211 ≤ 45226099643061^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479162373 10000000000 45226099643061 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252210963/10000000000 : ℝ)^4235 ≤ (42771868550281/100000000000000 : ℝ)^3211 := by
    have hnat : (5252210963 : ℕ)^4235*100000000000000^3211 ≤ 42771868550281^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252210963 10000000000 42771868550281 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001972893/5000000000 : ℝ), (5479162373/10000000000 : ℝ), (5252210963/10000000000 : ℝ)] ![(2400406357387/20000000000000 : ℝ), (45226099643061/100000000000000 : ℝ), (42771868550281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001972893/5000000000 : ℝ)|^4235 ≤ (2400406357387/20000000000000 : ℝ)^3211
        have hw : |(-1001972893/5000000000 : ℝ)|=(1001972893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479162373/10000000000 : ℝ)|^4235 ≤ (45226099643061/100000000000000 : ℝ)^3211
        have hw : |(5479162373/10000000000 : ℝ)|=(5479162373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252210963/10000000000 : ℝ)|^4235 ≤ (42771868550281/100000000000000 : ℝ)^3211
        have hw : |(5252210963/10000000000 : ℝ)|=(5252210963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_13 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383011593/10000000000 : ℝ)*x 0 + (-2134745231/10000000000 : ℝ)*x 1 + (2626105393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383011593/10000000000 : ℝ)^4235 ≤ (44182295353897/100000000000000 : ℝ)^3211 := by
    have hnat : (5383011593 : ℕ)^4235*100000000000000^3211 ≤ 44182295353897^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383011593 10000000000 44182295353897 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134745231/10000000000 : ℝ)^4235 ≤ (3261459496457/25000000000000 : ℝ)^3211 := by
    have hnat : (2134745231 : ℕ)^4235*25000000000000^3211 ≤ 3261459496457^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134745231 10000000000 3261459496457 25000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626105393/5000000000 : ℝ)^4235 ≤ (5346483331149/12500000000000 : ℝ)^3211 := by
    have hnat : (2626105393 : ℕ)^4235*12500000000000^3211 ≤ 5346483331149^3211*5000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626105393 5000000000 5346483331149 12500000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383011593/10000000000 : ℝ), (-2134745231/10000000000 : ℝ), (2626105393/5000000000 : ℝ)] ![(44182295353897/100000000000000 : ℝ), (3261459496457/25000000000000 : ℝ), (5346483331149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383011593/10000000000 : ℝ)|^4235 ≤ (44182295353897/100000000000000 : ℝ)^3211
        have hw : |(5383011593/10000000000 : ℝ)|=(5383011593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134745231/10000000000 : ℝ)|^4235 ≤ (3261459496457/25000000000000 : ℝ)^3211
        have hw : |(-2134745231/10000000000 : ℝ)|=(2134745231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626105393/5000000000 : ℝ)|^4235 ≤ (5346483331149/12500000000000 : ℝ)^3211
        have hw : |(2626105393/5000000000 : ℝ)|=(2626105393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_14 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345752837/2500000000 : ℝ)*x 0 + (1313052803/2500000000 : ℝ)*x 1 + (-66710781/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345752837/2500000000 : ℝ)^4235 ≤ (22091146350861/50000000000000 : ℝ)^3211 := by
    have hnat : (1345752837 : ℕ)^4235*50000000000000^3211 ≤ 22091146350861^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345752837 2500000000 22091146350861 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313052803/2500000000 : ℝ)^4235 ≤ (21385935612347/50000000000000 : ℝ)^3211 := by
    have hnat : (1313052803 : ℕ)^4235*50000000000000^3211 ≤ 21385935612347^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313052803 2500000000 21385935612347 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66710781/312500000 : ℝ)^4235 ≤ (1304583605947/10000000000000 : ℝ)^3211 := by
    have hnat : (66710781 : ℕ)^4235*10000000000000^3211 ≤ 1304583605947^3211*312500000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66710781 312500000 1304583605947 10000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345752837/2500000000 : ℝ), (1313052803/2500000000 : ℝ), (-66710781/312500000 : ℝ)] ![(22091146350861/50000000000000 : ℝ), (21385935612347/50000000000000 : ℝ), (1304583605947/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345752837/2500000000 : ℝ)|^4235 ≤ (22091146350861/50000000000000 : ℝ)^3211
        have hw : |(1345752837/2500000000 : ℝ)|=(1345752837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313052803/2500000000 : ℝ)|^4235 ≤ (21385935612347/50000000000000 : ℝ)^3211
        have hw : |(1313052803/2500000000 : ℝ)|=(1313052803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66710781/312500000 : ℝ)|^4235 ≤ (1304583605947/10000000000000 : ℝ)^3211
        have hw : |(-66710781/312500000 : ℝ)|=(66710781/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1275_box_15 (p : ℝ) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041940003/2500000000 : ℝ)*x 0 + (4436550111/10000000000 : ℝ)*x 1 + (554568661/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041940003/2500000000 : ℝ)^4235 ≤ (15763703137071/50000000000000 : ℝ)^3211 := by
    have hnat : (1041940003 : ℕ)^4235*50000000000000^3211 ≤ 15763703137071^3211*2500000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041940003 2500000000 15763703137071 50000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4436550111/10000000000 : ℝ)^4235 ≤ (684726020821/2000000000000 : ℝ)^3211 := by
    have hnat : (4436550111 : ℕ)^4235*2000000000000^3211 ≤ 684726020821^3211*10000000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436550111 10000000000 684726020821 2000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554568661/1250000000 : ℝ)^4235 ≤ (34236292664709/100000000000000 : ℝ)^3211 := by
    have hnat : (554568661 : ℕ)^4235*100000000000000^3211 ≤ 34236292664709^3211*1250000000^4235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554568661 1250000000 34236292664709 100000000000000 4235 3211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4235/1024 : ℝ)) 4235 3211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041940003/2500000000 : ℝ), (4436550111/10000000000 : ℝ), (554568661/1250000000 : ℝ)] ![(15763703137071/50000000000000 : ℝ), (684726020821/2000000000000 : ℝ), (34236292664709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041940003/2500000000 : ℝ)|^4235 ≤ (15763703137071/50000000000000 : ℝ)^3211
        have hw : |(1041940003/2500000000 : ℝ)|=(1041940003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4436550111/10000000000 : ℝ)|^4235 ≤ (684726020821/2000000000000 : ℝ)^3211
        have hw : |(4436550111/10000000000 : ℝ)|=(4436550111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554568661/1250000000 : ℝ)|^4235 ≤ (34236292664709/100000000000000 : ℝ)^3211
        have hw : |(554568661/1250000000 : ℝ)|=(554568661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1275_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(15709/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58813/100000 : ℝ) ∧ (79553/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84087/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (733/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (733/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (733/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (733/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (733/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (733/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1373/12500 : ℝ) ^ (2117/512 : ℝ) ≤ (10808603595797851/100000000000000000000 : ℝ) := by
    have hpowers : (1373/12500 : ℝ)^2117 ≤ (10808603595797851/100000000000000000000 : ℝ)^512 := by
      have hnat : (1373 : ℕ)^2117*100000000000000000000^512 ≤ 10808603595797851^512*12500^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1373 12500 10808603595797851 100000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1373/12500 : ℝ)) (X := (10808603595797851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hpowhi : (733/5000 : ℝ) ^ (2117/512 : ℝ) ≤ (17829099508975341/50000000000000000000 : ℝ) := by
    have hpowers : (733/5000 : ℝ)^2117 ≤ (17829099508975341/50000000000000000000 : ℝ)^512 := by
      have hnat : (733 : ℕ)^2117*50000000000000000000^512 ≤ 17829099508975341^512*5000^2117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        733 5000 17829099508975341 50000000000000000000 2117 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (733/5000 : ℝ)) (X := (17829099508975341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010808603595797851/50000000000000000000 : ℝ) ≤ (125006534661801/125000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (50010808603595797851/50000000000000000000 : ℝ)^512 ≤ (125006534661801/125000000000000 : ℝ)^2117 := by
      have hnat : (50010808603595797851 : ℕ)^512*125000000000000^2117 ≤ 125006534661801^2117*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010808603595797851 50000000000000000000 125006534661801 125000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125006534661801/125000000000000 : ℝ)) (X := (50010808603595797851/50000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046466802613748533/100000000000000000000 : ℝ) ≤ (2500280902378899/2500000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (100046466802613748533/100000000000000000000 : ℝ)^512 ≤ (2500280902378899/2500000000000000 : ℝ)^2117 := by
      have hnat : (100046466802613748533 : ℕ)^512*2500000000000000^2117 ≤ 2500280902378899^2117*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046466802613748533 100000000000000000000 2500280902378899 2500000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500280902378899/2500000000000000 : ℝ)) (X := (100046466802613748533/100000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017829099508975341/25000000000000000000 : ℝ) ≤ (1250215555760889/1250000000000000 : ℝ) ^ (2117/512 : ℝ) := by
    have hpowers : (25017829099508975341/25000000000000000000 : ℝ)^512 ≤ (1250215555760889/1250000000000000 : ℝ)^2117 := by
      have hnat : (25017829099508975341 : ℕ)^512*1250000000000000^2117 ≤ 1250215555760889^2117*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017829099508975341 25000000000000000000 1250215555760889 1250000000000000 512 2117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250215555760889/1250000000000000 : ℝ)) (X := (25017829099508975341/25000000000000000000 : ℝ)) (by norm_num) 2117 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10808603595797851/100000000000000000000 : ℝ) ≤ ((71774848702225341/71796875000000000 : ℝ)+2*(150209142879/91900000000000 : ℝ)*(1373/12500 : ℝ))^(2117/512 : ℝ) := by
    rw [show (71774848702225341/71796875000000000 : ℝ)+2*(150209142879/91900000000000 : ℝ)*(1373/12500 : ℝ)=(125006534661801/125000000000000 : ℝ) by norm_num, show 1+2*(10808603595797851/100000000000000000000 : ℝ)=(50010808603595797851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17829099508975341/50000000000000000000 : ℝ)+(10808603595797851/100000000000000000000 : ℝ) ≤ ((71774848702225341/71796875000000000 : ℝ)+(150209142879/91900000000000 : ℝ)*((733/5000 : ℝ)+(1373/12500 : ℝ)))^(2117/512 : ℝ) := by
    rw [show (71774848702225341/71796875000000000 : ℝ)+(150209142879/91900000000000 : ℝ)*((733/5000 : ℝ)+(1373/12500 : ℝ))=(2500280902378899/2500000000000000 : ℝ) by norm_num, show 1+(17829099508975341/50000000000000000000 : ℝ)+(10808603595797851/100000000000000000000 : ℝ)=(100046466802613748533/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17829099508975341/50000000000000000000 : ℝ) ≤ ((71774848702225341/71796875000000000 : ℝ)+2*(150209142879/91900000000000 : ℝ)*(733/5000 : ℝ))^(2117/512 : ℝ) := by
    rw [show (71774848702225341/71796875000000000 : ℝ)+2*(150209142879/91900000000000 : ℝ)*(733/5000 : ℝ)=(1250215555760889/1250000000000000 : ℝ) by norm_num, show 1+2*(17829099508975341/50000000000000000000 : ℝ)=(25017829099508975341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71774848702225341/71796875000000000 : ℝ)*(X 1 0+X 2 0)+(150209142879/91900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (733/5000 : ℝ)) (c := (71774848702225341/71796875000000000 : ℝ)) (alpha := (150209142879/91900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71774848702225341/71796875000000000 : ℝ)*(X 0 1+X 2 1)+(150209142879/91900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (733/5000 : ℝ)) (c := (71774848702225341/71796875000000000 : ℝ)) (alpha := (150209142879/91900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71774848702225341/71796875000000000 : ℝ)*(X 0 2+X 1 2)+(150209142879/91900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2117/512 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (733/5000 : ℝ)) (c := (71774848702225341/71796875000000000 : ℝ)) (alpha := (150209142879/91900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1930509539/10000000000 : ℝ)*X 0 0+(5392711207/10000000000 : ℝ)*X 0 1+(1348177441/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284045753/10000000000 : ℝ)*X 1 0+(-2079018079/10000000000 : ℝ)*X 1 1+(5392710887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321011619/2500000000 : ℝ)*X 2 0+(337044439/625000000 : ℝ)*X 2 1+(-51975423/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1123581881/2500000000 : ℝ)*X 0 0+(2136779741/5000000000 : ℝ)*X 0 1+(1068390079/2500000000 : ℝ)*X 0 2+(1123581881/2500000000 : ℝ)*X 1 0+(2136779741/5000000000 : ℝ)*X 1 1+(1068390079/2500000000 : ℝ)*X 1 2+(1123581881/2500000000 : ℝ)*X 2 0+(2136779741/5000000000 : ℝ)*X 2 1+(1068390079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2278866287/10000000000 : ℝ)*X 0 0+(2631608029/5000000000 : ℝ)*X 0 1+(2631607943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((215010497/400000000 : ℝ)*X 1 0+(-213047897/1000000000 : ℝ)*X 1 1+(5263216021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1075052443/2000000000 : ℝ)*X 2 0+(2631608091/5000000000 : ℝ)*X 2 1+(-1065239519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4193750589/10000000000 : ℝ)*X 0 0+(884758457/2000000000 : ℝ)*X 0 1+(4423792421/10000000000 : ℝ)*X 0 2+(4193750589/10000000000 : ℝ)*X 1 0+(884758457/2000000000 : ℝ)*X 1 1+(4423792421/10000000000 : ℝ)*X 1 2+(4193750589/10000000000 : ℝ)*X 2 0+(884758457/2000000000 : ℝ)*X 2 1+(4423792421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2205905951/10000000000 : ℝ)*X 0 0+(2587198749/5000000000 : ℝ)*X 0 1+(5406753821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274147889/10000000000 : ℝ)*X 1 0+(-2073299961/10000000000 : ℝ)*X 1 1+(5406753417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((210965927/400000000 : ℝ)*X 2 0+(5406753097/10000000000 : ℝ)*X 2 1+(-2073300009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4526363567/10000000000 : ℝ)*X 0 0+(4257254023/10000000000 : ℝ)*X 0 1+(1064313547/2500000000 : ℝ)*X 0 2+(4526363567/10000000000 : ℝ)*X 1 0+(4257254023/10000000000 : ℝ)*X 1 1+(1064313547/2500000000 : ℝ)*X 1 2+(4526363567/10000000000 : ℝ)*X 2 0+(4257254023/10000000000 : ℝ)*X 2 1+(1064313547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1001972893/5000000000 : ℝ)*X 0 0+(5479162373/10000000000 : ℝ)*X 0 1+(5252210963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5383011593/10000000000 : ℝ)*X 1 0+(-2134745231/10000000000 : ℝ)*X 1 1+(2626105393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1345752837/2500000000 : ℝ)*X 2 0+(1313052803/2500000000 : ℝ)*X 2 1+(-66710781/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1041940003/2500000000 : ℝ)*X 0 0+(4436550111/10000000000 : ℝ)*X 0 1+(554568661/1250000000 : ℝ)*X 0 2+(1041940003/2500000000 : ℝ)*X 1 0+(4436550111/10000000000 : ℝ)*X 1 1+(554568661/1250000000 : ℝ)*X 1 2+(1041940003/2500000000 : ℝ)*X 2 0+(4436550111/10000000000 : ℝ)*X 2 1+(554568661/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1275_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15709/25000 : ℝ) ≤ (-14435885452351551406720617/22975000000000000000000000 : ℝ) := by norm_num
    linear_combination (6951761/50000000000000 : ℝ)*(upper0) + (3352657/25000000000000 : ℝ)*(upper2) + (29934249/100000000000000 : ℝ)*(upper3) + (39329619/100000000000000 : ℝ)*(lower4) + (142225750083707/5000000000000 : ℝ)*(major0) + (142225750083707/5000000000000 : ℝ)*(major1) + (142225750083707/5000000000000 : ℝ)*(major2) + (454273699/100000000000000 : ℝ)*(sp3) + (1919874317398277/50000000000000 : ℝ)*(sp4) + (1919864366517519/50000000000000 : ℝ)*(sp5) + (479961592005983/12500000000000 : ℝ)*(sp6) + (935112626491459/50000000000000 : ℝ)*(sp7) + (3980352303/20000000000000 : ℝ)*(sp13) + (5589874869/10000000000000 : ℝ)*(sp14) + (233778213407077/12500000000000 : ℝ)*(f.failure) + (1919874317398277/50000000000000 : ℝ)*(f.sum) + (357119829601/114875000000000000000000000 : ℝ)*base66 + (13797353238858027/1435937500000000000000000000000 : ℝ)*base68 + (1636046620651731/179492187500000000000000000000 : ℝ)*base69 + (19116900863793321/2871875000000000000000000000000 : ℝ)*base71 + (30884499677/7352000000000000000000000 : ℝ)*base74 + (191531593945481/179492187500000000000000000000 : ℝ)*base75 + (48900913633701/717968750000000000000000000000 : ℝ)*base78 + (11419129709051777/1435937500000000000000000000000 : ℝ)*base80 + (1567918770931/459500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (737089/156250000000000000000 : ℝ)*base90 + (737089/156250000000000000000 : ℝ)*base92 + (737089/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58813/100000 : ℝ) ≤ (4222750754796351957696471332307/7179687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (447667681/100000000000000 : ℝ)*(lower1) + (447072171/100000000000000 : ℝ)*(lower2) + (6082899/5000000000000 : ℝ)*(upper4) + (2911012926837667/100000000000000 : ℝ)*(major0) + (2911012926837667/100000000000000 : ℝ)*(major1) + (2911012926837667/100000000000000 : ℝ)*(major2) + (486056690316371/12500000000000 : ℝ)*(sp0) + (1944222846314103/50000000000000 : ℝ)*(sp1) + (1944222595204603/50000000000000 : ℝ)*(sp2) + (478486254080661/25000000000000 : ℝ)*(sp3) + (14245887039/50000000000000 : ℝ)*(sp6) + (2073681773/100000000000000 : ℝ)*(sp7) + (4031930463/20000000000000 : ℝ)*(sp8) + (27989555077/100000000000000 : ℝ)*(sp9) + (1913947090004417/100000000000000 : ℝ)*(f.failure) + (3888473682183283/100000000000000 : ℝ)*(f.sum) + (11999783004873/4595000000000000000000000000 : ℝ)*base65 + (73607437105637163/28718750000000000000000000000000 : ℝ)*base67 + (104077110277331587/28718750000000000000000000000000 : ℝ)*base70 + (87848265845456587/28718750000000000000000000000000 : ℝ)*base72 + (5987831592697/4595000000000000000000000000 : ℝ)*base74 + (18402337184668413/28718750000000000000000000000000 : ℝ)*base75 + (232045949762487837/28718750000000000000000000000000 : ℝ)*base78 + (157892996381425337/28718750000000000000000000000000 : ℝ)*base80 + (13373354708379/2297500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7810531/1250000000000000000000 : ℝ)*base89 + (7810531/1250000000000000000000 : ℝ)*base91 + (7810531/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79553/100000 : ℝ) ≤ (5711812309860026128224804707643/7179687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1768027/2000000000000 : ℝ)*(lower3) + (4228997/50000000000000 : ℝ)*(upper4) + (7837633/100000000000000 : ℝ)*(lower5) + (1612752354685977/50000000000000 : ℝ)*(major0) + (1612752354685977/50000000000000 : ℝ)*(major1) + (1612752354685977/50000000000000 : ℝ)*(major2) + (1680241001/100000000000000 : ℝ)*(sp0) + (57906351011/50000000000000 : ℝ)*(sp1) + (102433647301/100000000000000 : ℝ)*(sp3) + (4303752755377757/100000000000000 : ℝ)*(sp8) + (4303654524108729/100000000000000 : ℝ)*(sp9) + (4303770336810751/100000000000000 : ℝ)*(sp10) + (1060309129807379/50000000000000 : ℝ)*(sp11) + (15901191993/100000000000000 : ℝ)*(sp12) + (2120720693262059/100000000000000 : ℝ)*(f.failure) + (4303770336810751/100000000000000 : ℝ)*(f.sum) + (284989031199/1148750000000000000000000000 : ℝ)*base65 + (143201434811549247/14359375000000000000000000000000 : ℝ)*base68 + (36283927180267997/14359375000000000000000000000000 : ℝ)*base70 + (3538831606094343/3589843750000000000000000000000 : ℝ)*base72 + (20655560874789/4595000000000000000000000000 : ℝ)*base74 + (3783866481173061/7179687500000000000000000000000 : ℝ)*base76 + (23171606040173061/7179687500000000000000000000000 : ℝ)*base78 + (9110340816608189/7179687500000000000000000000000 : ℝ)*base79 + (14303186939271/4595000000000000000000000000 : ℝ)*base81 + (1435263/1250000000000000000000 : ℝ)*base90 + (1435263/1250000000000000000000 : ℝ)*base92 + (1435263/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84087/100000 : ℝ) ≤ (-3018499313296389165424216919829/3589843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (143402717/50000000000000 : ℝ)*(lower0) + (6623401/5000000000000 : ℝ)*(lower1) + (43129237/100000000000000 : ℝ)*(lower2) + (1630600001437501/50000000000000 : ℝ)*(major0) + (1630600001437501/50000000000000 : ℝ)*(major1) + (1630600001437501/50000000000000 : ℝ)*(major2) + (420253709/2500000000000 : ℝ)*(sp0) + (405842316709/100000000000000 : ℝ)*(sp5) + (210877723073/100000000000000 : ℝ)*(sp6) + (39298381571/100000000000000 : ℝ)*(sp7) + (4406221525444847/100000000000000 : ℝ)*(sp12) + (4405832493276497/100000000000000 : ℝ)*(sp13) + (4406027457870133/100000000000000 : ℝ)*(sp14) + (268018813991869/12500000000000 : ℝ)*(sp15) + (2144189810316523/100000000000000 : ℝ)*(f.failure) + (2203119167796603/50000000000000 : ℝ)*(f.sum) + (4278423509963/4595000000000000000000000000 : ℝ)*base65 + (928971825491989/14359375000000000000000000000000 : ℝ)*base67 + (47730073749351761/14359375000000000000000000000000 : ℝ)*base70 + (1561338587772223/448730468750000000000000000000 : ℝ)*base72 + (99314294527/1148750000000000000000000000 : ℝ)*base73 + (117939106926116989/14359375000000000000000000000000 : ℝ)*base75 + (173985717799758011/14359375000000000000000000000000 : ℝ)*base78 + (40107140100224659/3589843750000000000000000000000 : ℝ)*base80 + (28917935167843/4595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9418111/1250000000000000000000 : ℝ)*base90 + (9418111/1250000000000000000000 : ℝ)*base92 + (9418111/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1275_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (733/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58813/100000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84087/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1275_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1275_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58813/100000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84087/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1275_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1275_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1275_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2117/512 : ℝ) ≤ p) (hpb : p ≤ (4235/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19011843/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58813/100000 : ℝ) else (79553/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84087/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1275_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
