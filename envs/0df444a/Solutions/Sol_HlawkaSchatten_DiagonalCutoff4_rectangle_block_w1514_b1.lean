-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:47.915021+00:00
-- url     : https://prove2.me/submissions/2bd36821-f57e-4764-8dfa-ddb917f30feb

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
theorem support_rectangle_w1514_s3_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1864579019/10000000000 : ℝ)*x 0 + (5436173821/10000000000 : ℝ)*x 1 + (2607429421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1864579019/10000000000 : ℝ)^4525 ≤ (1140865716849/10000000000000 : ℝ)^3501 := by
    have hnat : (1864579019 : ℕ)^4525*10000000000000^3501 ≤ 1140865716849^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864579019 10000000000 1140865716849 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436173821/10000000000 : ℝ)^4525 ≤ (2842823297701/6250000000000 : ℝ)^3501 := by
    have hnat : (5436173821 : ℕ)^4525*6250000000000^3501 ≤ 2842823297701^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436173821 10000000000 2842823297701 6250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607429421/5000000000 : ℝ)^4525 ≤ (2155308502089/5000000000000 : ℝ)^3501 := by
    have hnat : (2607429421 : ℕ)^4525*5000000000000^3501 ≤ 2155308502089^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607429421 5000000000 2155308502089 5000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1864579019/10000000000 : ℝ), (5436173821/10000000000 : ℝ), (2607429421/5000000000 : ℝ)] ![(1140865716849/10000000000000 : ℝ), (2842823297701/6250000000000 : ℝ), (2155308502089/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1864579019/10000000000 : ℝ)|^4525 ≤ (1140865716849/10000000000000 : ℝ)^3501
        have hw : |(-1864579019/10000000000 : ℝ)|=(1864579019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436173821/10000000000 : ℝ)|^4525 ≤ (2842823297701/6250000000000 : ℝ)^3501
        have hw : |(5436173821/10000000000 : ℝ)|=(5436173821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607429421/5000000000 : ℝ)|^4525 ≤ (2155308502089/5000000000000 : ℝ)^3501
        have hw : |(2607429421/5000000000 : ℝ)|=(2607429421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352317513/10000000000 : ℝ)*x 0 + (-1977996933/10000000000 : ℝ)*x 1 + (521485879/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352317513/10000000000 : ℝ)^4525 ≤ (22290184606981/50000000000000 : ℝ)^3501 := by
    have hnat : (5352317513 : ℕ)^4525*50000000000000^3501 ≤ 22290184606981^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352317513 10000000000 22290184606981 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1977996933/10000000000 : ℝ)^4525 ≤ (12313461286661/100000000000000 : ℝ)^3501 := by
    have hnat : (1977996933 : ℕ)^4525*100000000000000^3501 ≤ 12313461286661^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977996933 10000000000 12313461286661 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521485879/1000000000 : ℝ)^4525 ≤ (1724246779449/4000000000000 : ℝ)^3501 := by
    have hnat : (521485879 : ℕ)^4525*4000000000000^3501 ≤ 1724246779449^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521485879 1000000000 1724246779449 4000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352317513/10000000000 : ℝ), (-1977996933/10000000000 : ℝ), (521485879/1000000000 : ℝ)] ![(22290184606981/50000000000000 : ℝ), (12313461286661/100000000000000 : ℝ), (1724246779449/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352317513/10000000000 : ℝ)|^4525 ≤ (22290184606981/50000000000000 : ℝ)^3501
        have hw : |(5352317513/10000000000 : ℝ)|=(5352317513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1977996933/10000000000 : ℝ)|^4525 ≤ (12313461286661/100000000000000 : ℝ)^3501
        have hw : |(-1977996933/10000000000 : ℝ)|=(1977996933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521485879/1000000000 : ℝ)|^4525 ≤ (1724246779449/4000000000000 : ℝ)^3501
        have hw : |(521485879/1000000000 : ℝ)|=(521485879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352317497/10000000000 : ℝ)*x 0 + (1042971761/2000000000 : ℝ)*x 1 + (-988998467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352317497/10000000000 : ℝ)^4525 ≤ (11145092260429/25000000000000 : ℝ)^3501 := by
    have hnat : (5352317497 : ℕ)^4525*25000000000000^3501 ≤ 11145092260429^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352317497 10000000000 11145092260429 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042971761/2000000000 : ℝ)^4525 ≤ (43106169646481/100000000000000 : ℝ)^3501 := by
    have hnat : (1042971761 : ℕ)^4525*100000000000000^3501 ≤ 43106169646481^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042971761 2000000000 43106169646481 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988998467/5000000000 : ℝ)^4525 ≤ (12313461294707/100000000000000 : ℝ)^3501 := by
    have hnat : (988998467 : ℕ)^4525*100000000000000^3501 ≤ 12313461294707^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988998467 5000000000 12313461294707 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352317497/10000000000 : ℝ), (1042971761/2000000000 : ℝ), (-988998467/5000000000 : ℝ)] ![(11145092260429/25000000000000 : ℝ), (43106169646481/100000000000000 : ℝ), (12313461294707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352317497/10000000000 : ℝ)|^4525 ≤ (11145092260429/25000000000000 : ℝ)^3501
        have hw : |(5352317497/10000000000 : ℝ)|=(5352317497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042971761/2000000000 : ℝ)|^4525 ≤ (43106169646481/100000000000000 : ℝ)^3501
        have hw : |(1042971761/2000000000 : ℝ)|=(1042971761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988998467/5000000000 : ℝ)|^4525 ≤ (12313461294707/100000000000000 : ℝ)^3501
        have hw : |(-988998467/5000000000 : ℝ)|=(988998467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853707469/2000000000 : ℝ)*x 0 + (201176337/500000000 : ℝ)*x 1 + (4526084607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853707469/2000000000 : ℝ)^4525 ≤ (33276696521557/100000000000000 : ℝ)^3501 := by
    have hnat : (853707469 : ℕ)^4525*100000000000000^3501 ≤ 33276696521557^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853707469 2000000000 33276696521557 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201176337/500000000 : ℝ)^4525 ≤ (3082898366843/10000000000000 : ℝ)^3501 := by
    have hnat : (201176337 : ℕ)^4525*10000000000000^3501 ≤ 3082898366843^3501*500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201176337 500000000 3082898366843 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526084607/10000000000 : ℝ)^4525 ≤ (8973579948623/25000000000000 : ℝ)^3501 := by
    have hnat : (4526084607 : ℕ)^4525*25000000000000^3501 ≤ 8973579948623^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526084607 10000000000 8973579948623 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853707469/2000000000 : ℝ), (201176337/500000000 : ℝ), (4526084607/10000000000 : ℝ)] ![(33276696521557/100000000000000 : ℝ), (3082898366843/10000000000000 : ℝ), (8973579948623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853707469/2000000000 : ℝ)|^4525 ≤ (33276696521557/100000000000000 : ℝ)^3501
        have hw : |(853707469/2000000000 : ℝ)|=(853707469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201176337/500000000 : ℝ)|^4525 ≤ (3082898366843/10000000000000 : ℝ)^3501
        have hw : |(201176337/500000000 : ℝ)|=(201176337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526084607/10000000000 : ℝ)|^4525 ≤ (8973579948623/25000000000000 : ℝ)^3501
        have hw : |(4526084607/10000000000 : ℝ)|=(4526084607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372922081/2000000000 : ℝ)*x 0 + (130400763/250000000 : ℝ)*x 1 + (2717496637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372922081/2000000000 : ℝ)^4525 ≤ (2852226344333/25000000000000 : ℝ)^3501 := by
    have hnat : (372922081 : ℕ)^4525*25000000000000^3501 ≤ 2852226344333^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372922081 2000000000 2852226344333 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130400763/250000000 : ℝ)^4525 ≤ (43118688357423/100000000000000 : ℝ)^3501 := by
    have hnat : (130400763 : ℕ)^4525*100000000000000^3501 ≤ 43118688357423^3501*250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130400763 250000000 43118688357423 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717496637/5000000000 : ℝ)^4525 ≤ (22736203122419/50000000000000 : ℝ)^3501 := by
    have hnat : (2717496637 : ℕ)^4525*50000000000000^3501 ≤ 22736203122419^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717496637 5000000000 22736203122419 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372922081/2000000000 : ℝ), (130400763/250000000 : ℝ), (2717496637/5000000000 : ℝ)] ![(2852226344333/25000000000000 : ℝ), (43118688357423/100000000000000 : ℝ), (22736203122419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372922081/2000000000 : ℝ)|^4525 ≤ (2852226344333/25000000000000 : ℝ)^3501
        have hw : |(-372922081/2000000000 : ℝ)|=(372922081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130400763/250000000 : ℝ)|^4525 ≤ (43118688357423/100000000000000 : ℝ)^3501
        have hw : |(130400763/250000000 : ℝ)|=(130400763/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717496637/5000000000 : ℝ)|^4525 ≤ (22736203122419/50000000000000 : ℝ)^3501
        have hw : |(2717496637/5000000000 : ℝ)|=(2717496637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294200523/10000000000 : ℝ)*x 0 + (-878931143/5000000000 : ℝ)*x 1 + (5434993443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294200523/10000000000 : ℝ)^4525 ≤ (43955715378107/100000000000000 : ℝ)^3501 := by
    have hnat : (5294200523 : ℕ)^4525*100000000000000^3501 ≤ 43955715378107^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294200523 10000000000 43955715378107 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878931143/5000000000 : ℝ)^4525 ≤ (10571876530583/100000000000000 : ℝ)^3501 := by
    have hnat : (878931143 : ℕ)^4525*100000000000000^3501 ≤ 10571876530583^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878931143 5000000000 10571876530583 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434993443/10000000000 : ℝ)^4525 ≤ (45472408072357/100000000000000 : ℝ)^3501 := by
    have hnat : (5434993443 : ℕ)^4525*100000000000000^3501 ≤ 45472408072357^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434993443 10000000000 45472408072357 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294200523/10000000000 : ℝ), (-878931143/5000000000 : ℝ), (5434993443/10000000000 : ℝ)] ![(43955715378107/100000000000000 : ℝ), (10571876530583/100000000000000 : ℝ), (45472408072357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294200523/10000000000 : ℝ)|^4525 ≤ (43955715378107/100000000000000 : ℝ)^3501
        have hw : |(5294200523/10000000000 : ℝ)|=(5294200523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878931143/5000000000 : ℝ)|^4525 ≤ (10571876530583/100000000000000 : ℝ)^3501
        have hw : |(-878931143/5000000000 : ℝ)|=(878931143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434993443/10000000000 : ℝ)|^4525 ≤ (45472408072357/100000000000000 : ℝ)^3501
        have hw : |(5434993443/10000000000 : ℝ)|=(5434993443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294200691/10000000000 : ℝ)*x 0 + (5434993199/10000000000 : ℝ)*x 1 + (-351572479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294200691/10000000000 : ℝ)^4525 ≤ (1098892929523/2500000000000 : ℝ)^3501 := by
    have hnat : (5294200691 : ℕ)^4525*2500000000000^3501 ≤ 1098892929523^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294200691 10000000000 1098892929523 2500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434993199/10000000000 : ℝ)^4525 ≤ (2842025339613/6250000000000 : ℝ)^3501 := by
    have hnat : (5434993199 : ℕ)^4525*6250000000000^3501 ≤ 2842025339613^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434993199 10000000000 2842025339613 6250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351572479/2000000000 : ℝ)^4525 ≤ (211437547557/2000000000000 : ℝ)^3501 := by
    have hnat : (351572479 : ℕ)^4525*2000000000000^3501 ≤ 211437547557^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351572479 2000000000 211437547557 2000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294200691/10000000000 : ℝ), (5434993199/10000000000 : ℝ), (-351572479/2000000000 : ℝ)] ![(1098892929523/2500000000000 : ℝ), (2842025339613/6250000000000 : ℝ), (211437547557/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294200691/10000000000 : ℝ)|^4525 ≤ (1098892929523/2500000000000 : ℝ)^3501
        have hw : |(5294200691/10000000000 : ℝ)|=(5294200691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434993199/10000000000 : ℝ)|^4525 ≤ (2842025339613/6250000000000 : ℝ)^3501
        have hw : |(5434993199/10000000000 : ℝ)|=(5434993199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-351572479/2000000000 : ℝ)|^4525 ≤ (211437547557/2000000000000 : ℝ)^3501
        have hw : |(-351572479/2000000000 : ℝ)|=(351572479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s3_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067152207/2500000000 : ℝ)*x 0 + (2261712043/5000000000 : ℝ)*x 1 + (2013103609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067152207/2500000000 : ℝ)^4525 ≤ (8319354196273/25000000000000 : ℝ)^3501 := by
    have hnat : (1067152207 : ℕ)^4525*25000000000000^3501 ≤ 8319354196273^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067152207 2500000000 8319354196273 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261712043/5000000000 : ℝ)^4525 ≤ (35867051443041/100000000000000 : ℝ)^3501 := by
    have hnat : (2261712043 : ℕ)^4525*100000000000000^3501 ≤ 35867051443041^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261712043 5000000000 35867051443041 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013103609/5000000000 : ℝ)^4525 ≤ (30855531761977/100000000000000 : ℝ)^3501 := by
    have hnat : (2013103609 : ℕ)^4525*100000000000000^3501 ≤ 30855531761977^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013103609 5000000000 30855531761977 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067152207/2500000000 : ℝ), (2261712043/5000000000 : ℝ), (2013103609/5000000000 : ℝ)] ![(8319354196273/25000000000000 : ℝ), (35867051443041/100000000000000 : ℝ), (30855531761977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067152207/2500000000 : ℝ)|^4525 ≤ (8319354196273/25000000000000 : ℝ)^3501
        have hw : |(1067152207/2500000000 : ℝ)|=(1067152207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261712043/5000000000 : ℝ)|^4525 ≤ (35867051443041/100000000000000 : ℝ)^3501
        have hw : |(2261712043/5000000000 : ℝ)|=(2261712043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2013103609/5000000000 : ℝ)|^4525 ≤ (30855531761977/100000000000000 : ℝ)^3501
        have hw : |(2013103609/5000000000 : ℝ)|=(2013103609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5431/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15549/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5229/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5229/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5229/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5229/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5229/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5229/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5229/50000 : ℝ) ^ (4523/1024 : ℝ) ≤ (466565145967007/10000000000000000000 : ℝ) := by
    have hpowers : (5229/50000 : ℝ)^4523 ≤ (466565145967007/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5229 : ℕ)^4523*10000000000000000000^1024 ≤ 466565145967007^1024*50000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5229 50000 466565145967007 10000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5229/50000 : ℝ)) (X := (466565145967007/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15989/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (7607201535183091/25000000000000000000 : ℝ) := by
    have hpowers : (15989/100000 : ℝ)^4523 ≤ (7607201535183091/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15989 : ℕ)^4523*25000000000000000000^1024 ≤ 7607201535183091^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15989 100000 7607201535183091 25000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15989/100000 : ℝ)) (X := (7607201535183091/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000466565145967007/5000000000000000000 : ℝ) ≤ (10000211251588003/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (5000466565145967007/5000000000000000000 : ℝ)^1024 ≤ (10000211251588003/10000000000000000 : ℝ)^4523 := by
      have hnat : (5000466565145967007 : ℕ)^1024*10000000000000000^4523 ≤ 10000211251588003^4523*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000466565145967007 5000000000000000000 10000211251588003 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000211251588003/10000000000000000 : ℝ)) (X := (5000466565145967007/5000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017547228800201217/50000000000000000000 : ℝ) ≤ (10000794425101503/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (50017547228800201217/50000000000000000000 : ℝ)^1024 ≤ (10000794425101503/10000000000000000 : ℝ)^4523 := by
      have hnat : (50017547228800201217 : ℕ)^1024*10000000000000000^4523 ≤ 10000794425101503^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017547228800201217 50000000000000000000 10000794425101503 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000794425101503/10000000000000000 : ℝ)) (X := (50017547228800201217/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507607201535183091/12500000000000000000 : ℝ) ≤ (10001377598615003/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (12507607201535183091/12500000000000000000 : ℝ)^1024 ≤ (10001377598615003/10000000000000000 : ℝ)^4523 := by
      have hnat : (12507607201535183091 : ℕ)^1024*10000000000000000^4523 ≤ 10001377598615003^4523*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507607201535183091 12500000000000000000 10001377598615003 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001377598615003/10000000000000000 : ℝ)) (X := (12507607201535183091/12500000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(466565145967007/10000000000000000000 : ℝ) ≤ ((55298970775324878593/55310000000000000000 : ℝ)+2*(1166347027/1106200000000 : ℝ)*(5229/50000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (55298970775324878593/55310000000000000000 : ℝ)+2*(1166347027/1106200000000 : ℝ)*(5229/50000 : ℝ)=(10000211251588003/10000000000000000 : ℝ) by norm_num, show 1+2*(466565145967007/10000000000000000000 : ℝ)=(5000466565145967007/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7607201535183091/25000000000000000000 : ℝ)+(466565145967007/10000000000000000000 : ℝ) ≤ ((55298970775324878593/55310000000000000000 : ℝ)+(1166347027/1106200000000 : ℝ)*((15989/100000 : ℝ)+(5229/50000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (55298970775324878593/55310000000000000000 : ℝ)+(1166347027/1106200000000 : ℝ)*((15989/100000 : ℝ)+(5229/50000 : ℝ))=(10000794425101503/10000000000000000 : ℝ) by norm_num, show 1+(7607201535183091/25000000000000000000 : ℝ)+(466565145967007/10000000000000000000 : ℝ)=(50017547228800201217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7607201535183091/25000000000000000000 : ℝ) ≤ ((55298970775324878593/55310000000000000000 : ℝ)+2*(1166347027/1106200000000 : ℝ)*(15989/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (55298970775324878593/55310000000000000000 : ℝ)+2*(1166347027/1106200000000 : ℝ)*(15989/100000 : ℝ)=(10001377598615003/10000000000000000 : ℝ) by norm_num, show 1+2*(7607201535183091/25000000000000000000 : ℝ)=(12507607201535183091/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55298970775324878593/55310000000000000000 : ℝ)*(X 1 0+X 2 0)+(1166347027/1106200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (5229/50000 : ℝ)) (hi := (15989/100000 : ℝ)) (c := (55298970775324878593/55310000000000000000 : ℝ)) (alpha := (1166347027/1106200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55298970775324878593/55310000000000000000 : ℝ)*(X 0 1+X 2 1)+(1166347027/1106200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (5229/50000 : ℝ)) (hi := (15989/100000 : ℝ)) (c := (55298970775324878593/55310000000000000000 : ℝ)) (alpha := (1166347027/1106200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55298970775324878593/55310000000000000000 : ℝ)*(X 0 2+X 1 2)+(1166347027/1106200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (5229/50000 : ℝ)) (hi := (15989/100000 : ℝ)) (c := (55298970775324878593/55310000000000000000 : ℝ)) (alpha := (1166347027/1106200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1864579019/10000000000 : ℝ)*X 0 0+(5436173821/10000000000 : ℝ)*X 0 1+(2607429421/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352317513/10000000000 : ℝ)*X 1 0+(-1977996933/10000000000 : ℝ)*X 1 1+(521485879/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352317497/10000000000 : ℝ)*X 2 0+(1042971761/2000000000 : ℝ)*X 2 1+(-988998467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((853707469/2000000000 : ℝ)*X 0 0+(201176337/500000000 : ℝ)*X 0 1+(4526084607/10000000000 : ℝ)*X 0 2+(853707469/2000000000 : ℝ)*X 1 0+(201176337/500000000 : ℝ)*X 1 1+(4526084607/10000000000 : ℝ)*X 1 2+(853707469/2000000000 : ℝ)*X 2 0+(201176337/500000000 : ℝ)*X 2 1+(4526084607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372922081/2000000000 : ℝ)*X 0 0+(130400763/250000000 : ℝ)*X 0 1+(2717496637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294200523/10000000000 : ℝ)*X 1 0+(-878931143/5000000000 : ℝ)*X 1 1+(5434993443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294200691/10000000000 : ℝ)*X 2 0+(5434993199/10000000000 : ℝ)*X 2 1+(-351572479/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1067152207/2500000000 : ℝ)*X 0 0+(2261712043/5000000000 : ℝ)*X 0 1+(2013103609/5000000000 : ℝ)*X 0 2+(1067152207/2500000000 : ℝ)*X 1 0+(2261712043/5000000000 : ℝ)*X 1 1+(2013103609/5000000000 : ℝ)*X 1 2+(1067152207/2500000000 : ℝ)*X 2 0+(2261712043/5000000000 : ℝ)*X 2 1+(2013103609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9426744818786978837014666977/1382750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62026419/5000000000000 : ℝ)*(base19) + (142190067/12500000000000 : ℝ)*(base23) + (9580699/20000000000000 : ℝ)*(lower2) + (8342953/5000000000000 : ℝ)*(upper3) + (3897107/4000000000000 : ℝ)*(upper5) + (3254161003084837/100000000000000 : ℝ)*(major0) + (3254161003084837/100000000000000 : ℝ)*(major1) + (3254161003084837/100000000000000 : ℝ)*(major2) + (2259233163500033/50000000000000 : ℝ)*(sp0) + (4518483405058321/100000000000000 : ℝ)*(sp1) + (903696701613233/20000000000000 : ℝ)*(sp2) + (994914169951287/50000000000000 : ℝ)*(sp3) + (3663717327/20000000000000 : ℝ)*(sp4) + (1099179261/12500000000000 : ℝ)*(sp7) + (994918566668331/50000000000000 : ℝ)*(f.failure) + (4518484645586701/100000000000000 : ℝ)*(f.sum) + (1370541214803/1106200000000000000000000000 : ℝ)*base66 + (14590783512320194341/5531000000000000000000000000000000 : ℝ)*base67 + (8891876456370194341/5531000000000000000000000000000000 : ℝ)*base69 + (47687259559377194341/5531000000000000000000000000000000 : ℝ)*base71 + (7685771052097/1106200000000000000000000000 : ℝ)*base74 + (34269365163497805659/5531000000000000000000000000000000 : ℝ)*base76 + (40560492320085194341/5531000000000000000000000000000000 : ℝ)*base77 + (106437129024211194341/5531000000000000000000000000000000 : ℝ)*base79 + (2181408541147/345687500000000000000000000 : ℝ)*base82 + (33513853/5000000000000000000000 : ℝ)*base89 + (33513853/5000000000000000000000 : ℝ)*base91 + (33513853/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10715269947108251822390742297/1382750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33907679/2500000000000 : ℝ)*(base19) + (854012641/50000000000000 : ℝ)*(base23) + (12435483/6250000000000 : ℝ)*(upper3) + (96439499/100000000000000 : ℝ)*(lower4) + (7108571/5000000000000 : ℝ)*(upper5) + (1644544919137757/50000000000000 : ℝ)*(major0) + (1644544919137757/50000000000000 : ℝ)*(major1) + (1644544919137757/50000000000000 : ℝ)*(major2) + (5648467963/25000000000000 : ℝ)*(sp1) + (24838013943/100000000000000 : ℝ)*(sp2) + (913396837155371/20000000000000 : ℝ)*(sp4) + (4566960235597843/100000000000000 : ℝ)*(sp5) + (456695763973763/10000000000000 : ℝ)*(sp6) + (2011195232465967/100000000000000 : ℝ)*(sp7) + (2011195232465967/100000000000000 : ℝ)*(f.failure) + (913396837155371/20000000000000 : ℝ)*(f.sum) + (15145645489869/5531000000000000000000000000 : ℝ)*base65 + (12244713840406335901/2765500000000000000000000000000000 : ℝ)*base67 + (22842089846460664099/2765500000000000000000000000000000 : ℝ)*base70 + (4175325331531835901/2765500000000000000000000000000000 : ℝ)*base71 + (1747101601803/1382750000000000000000000000 : ℝ)*base73 + (15775769027774835901/2765500000000000000000000000000000 : ℝ)*base75 + (20525107803473835901/2765500000000000000000000000000000 : ℝ)*base77 + (29157813112561164099/2765500000000000000000000000000000 : ℝ)*base80 + (16828552105107/2765500000000000000000000000 : ℝ)*base82 + (22568921/10000000000000000000000 : ℝ)*base89 + (22568921/10000000000000000000000 : ℝ)*base91 + (22568921/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1514_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5431/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15549/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1514_s4_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865008193/10000000000 : ℝ)*x 0 + (108667167/200000000 : ℝ)*x 1 + (652173833/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865008193/10000000000 : ℝ)^4525 ≤ (2282410259321/20000000000000 : ℝ)^3501 := by
    have hnat : (1865008193 : ℕ)^4525*20000000000000^3501 ≤ 2282410259321^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865008193 10000000000 2282410259321 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108667167/200000000 : ℝ)^4525 ≤ (1420460231281/3125000000000 : ℝ)^3501 := by
    have hnat : (108667167 : ℕ)^4525*3125000000000^3501 ≤ 1420460231281^3501*200000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108667167 200000000 1420460231281 3125000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652173833/1250000000 : ℝ)^4525 ≤ (10783305323187/25000000000000 : ℝ)^3501 := by
    have hnat : (652173833 : ℕ)^4525*25000000000000^3501 ≤ 10783305323187^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652173833 1250000000 10783305323187 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865008193/10000000000 : ℝ), (108667167/200000000 : ℝ), (652173833/1250000000 : ℝ)] ![(2282410259321/20000000000000 : ℝ), (1420460231281/3125000000000 : ℝ), (10783305323187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865008193/10000000000 : ℝ)|^4525 ≤ (2282410259321/20000000000000 : ℝ)^3501
        have hw : |(-1865008193/10000000000 : ℝ)|=(1865008193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108667167/200000000 : ℝ)|^4525 ≤ (1420460231281/3125000000000 : ℝ)^3501
        have hw : |(108667167/200000000 : ℝ)|=(108667167/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652173833/1250000000 : ℝ)|^4525 ≤ (10783305323187/25000000000000 : ℝ)^3501
        have hw : |(652173833/1250000000 : ℝ)|=(652173833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337895159/2500000000 : ℝ)*x 0 + (-19756213/100000000 : ℝ)*x 1 + (5217389897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337895159/2500000000 : ℝ)^4525 ≤ (44572436632851/100000000000000 : ℝ)^3501 := by
    have hnat : (1337895159 : ℕ)^4525*100000000000000^3501 ≤ 44572436632851^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337895159 2500000000 44572436632851 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19756213/100000000 : ℝ)^4525 ≤ (12294350258677/100000000000000 : ℝ)^3501 := by
    have hnat : (19756213 : ℕ)^4525*100000000000000^3501 ≤ 12294350258677^3501*100000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19756213 100000000 12294350258677 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217389897/10000000000 : ℝ)^4525 ≤ (8626642619431/20000000000000 : ℝ)^3501 := by
    have hnat : (5217389897 : ℕ)^4525*20000000000000^3501 ≤ 8626642619431^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217389897 10000000000 8626642619431 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337895159/2500000000 : ℝ), (-19756213/100000000 : ℝ), (5217389897/10000000000 : ℝ)] ![(44572436632851/100000000000000 : ℝ), (12294350258677/100000000000000 : ℝ), (8626642619431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337895159/2500000000 : ℝ)|^4525 ≤ (44572436632851/100000000000000 : ℝ)^3501
        have hw : |(1337895159/2500000000 : ℝ)|=(1337895159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19756213/100000000 : ℝ)|^4525 ≤ (12294350258677/100000000000000 : ℝ)^3501
        have hw : |(-19756213/100000000 : ℝ)|=(19756213/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217389897/10000000000 : ℝ)|^4525 ≤ (8626642619431/20000000000000 : ℝ)^3501
        have hw : |(5217389897/10000000000 : ℝ)|=(5217389897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351580141/10000000000 : ℝ)*x 0 + (5217390641/10000000000 : ℝ)*x 1 + (-987810487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351580141/10000000000 : ℝ)^4525 ≤ (5571553913027/12500000000000 : ℝ)^3501 := by
    have hnat : (5351580141 : ℕ)^4525*12500000000000^3501 ≤ 5571553913027^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351580141 10000000000 5571553913027 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217390641/10000000000 : ℝ)^4525 ≤ (43133221046987/100000000000000 : ℝ)^3501 := by
    have hnat : (5217390641 : ℕ)^4525*100000000000000^3501 ≤ 43133221046987^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217390641 10000000000 43133221046987 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987810487/5000000000 : ℝ)^4525 ≤ (12294347636597/100000000000000 : ℝ)^3501 := by
    have hnat : (987810487 : ℕ)^4525*100000000000000^3501 ≤ 12294347636597^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987810487 5000000000 12294347636597 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351580141/10000000000 : ℝ), (5217390641/10000000000 : ℝ), (-987810487/5000000000 : ℝ)] ![(5571553913027/12500000000000 : ℝ), (43133221046987/100000000000000 : ℝ), (12294347636597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351580141/10000000000 : ℝ)|^4525 ≤ (5571553913027/12500000000000 : ℝ)^3501
        have hw : |(5351580141/10000000000 : ℝ)|=(5351580141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217390641/10000000000 : ℝ)|^4525 ≤ (43133221046987/100000000000000 : ℝ)^3501
        have hw : |(5217390641/10000000000 : ℝ)|=(5217390641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987810487/5000000000 : ℝ)|^4525 ≤ (12294347636597/100000000000000 : ℝ)^3501
        have hw : |(-987810487/5000000000 : ℝ)|=(987810487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268805127/10000000000 : ℝ)*x 0 + (4029566683/10000000000 : ℝ)*x 1 + (2259991667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268805127/10000000000 : ℝ)^4525 ≤ (33279394714231/100000000000000 : ℝ)^3501 := by
    have hnat : (4268805127 : ℕ)^4525*100000000000000^3501 ≤ 33279394714231^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268805127 10000000000 33279394714231 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029566683/10000000000 : ℝ)^4525 ≤ (386110150061/1250000000000 : ℝ)^3501 := by
    have hnat : (4029566683 : ℕ)^4525*1250000000000^3501 ≤ 386110150061^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029566683 10000000000 386110150061 1250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259991667/5000000000 : ℝ)^4525 ≤ (35831793263037/100000000000000 : ℝ)^3501 := by
    have hnat : (2259991667 : ℕ)^4525*100000000000000^3501 ≤ 35831793263037^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259991667 5000000000 35831793263037 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268805127/10000000000 : ℝ), (4029566683/10000000000 : ℝ), (2259991667/5000000000 : ℝ)] ![(33279394714231/100000000000000 : ℝ), (386110150061/1250000000000 : ℝ), (35831793263037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268805127/10000000000 : ℝ)|^4525 ≤ (33279394714231/100000000000000 : ℝ)^3501
        have hw : |(4268805127/10000000000 : ℝ)|=(4268805127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029566683/10000000000 : ℝ)|^4525 ≤ (386110150061/1250000000000 : ℝ)^3501
        have hw : |(4029566683/10000000000 : ℝ)|=(4029566683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259991667/5000000000 : ℝ)|^4525 ≤ (35831793263037/100000000000000 : ℝ)^3501
        have hw : |(2259991667/5000000000 : ℝ)|=(2259991667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37300751/200000000 : ℝ)*x 0 + (521850623/1000000000 : ℝ)*x 1 + (5432234399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37300751/200000000 : ℝ)^4525 ≤ (11412283475167/100000000000000 : ℝ)^3501 := by
    have hnat : (37300751 : ℕ)^4525*100000000000000^3501 ≤ 11412283475167^3501*200000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37300751 200000000 11412283475167 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521850623/1000000000 : ℝ)^4525 ≤ (431451417759/1000000000000 : ℝ)^3501 := by
    have hnat : (521850623 : ℕ)^4525*1000000000000^3501 ≤ 431451417759^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521850623 1000000000 431451417759 1000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432234399/10000000000 : ℝ)^4525 ≤ (4544257473897/10000000000000 : ℝ)^3501 := by
    have hnat : (5432234399 : ℕ)^4525*10000000000000^3501 ≤ 4544257473897^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432234399 10000000000 4544257473897 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37300751/200000000 : ℝ), (521850623/1000000000 : ℝ), (5432234399/10000000000 : ℝ)] ![(11412283475167/100000000000000 : ℝ), (431451417759/1000000000000 : ℝ), (4544257473897/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37300751/200000000 : ℝ)|^4525 ≤ (11412283475167/100000000000000 : ℝ)^3501
        have hw : |(-37300751/200000000 : ℝ)|=(37300751/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521850623/1000000000 : ℝ)|^4525 ≤ (431451417759/1000000000000 : ℝ)^3501
        have hw : |(521850623/1000000000 : ℝ)|=(521850623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432234399/10000000000 : ℝ)|^4525 ≤ (4544257473897/10000000000000 : ℝ)^3501
        have hw : |(5432234399/10000000000 : ℝ)|=(5432234399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294868633/10000000000 : ℝ)*x 0 + (-1760777233/10000000000 : ℝ)*x 1 + (1358058601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294868633/10000000000 : ℝ)^4525 ≤ (8792577003873/20000000000000 : ℝ)^3501 := by
    have hnat : (5294868633 : ℕ)^4525*20000000000000^3501 ≤ 8792577003873^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294868633 10000000000 8792577003873 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760777233/10000000000 : ℝ)^4525 ≤ (10594540169099/100000000000000 : ℝ)^3501 := by
    have hnat : (1760777233 : ℕ)^4525*100000000000000^3501 ≤ 10594540169099^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760777233 10000000000 10594540169099 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358058601/2500000000 : ℝ)^4525 ≤ (45442574793031/100000000000000 : ℝ)^3501 := by
    have hnat : (1358058601 : ℕ)^4525*100000000000000^3501 ≤ 45442574793031^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358058601 2500000000 45442574793031 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294868633/10000000000 : ℝ), (-1760777233/10000000000 : ℝ), (1358058601/2500000000 : ℝ)] ![(8792577003873/20000000000000 : ℝ), (10594540169099/100000000000000 : ℝ), (45442574793031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294868633/10000000000 : ℝ)|^4525 ≤ (8792577003873/20000000000000 : ℝ)^3501
        have hw : |(5294868633/10000000000 : ℝ)|=(5294868633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760777233/10000000000 : ℝ)|^4525 ≤ (10594540169099/100000000000000 : ℝ)^3501
        have hw : |(-1760777233/10000000000 : ℝ)|=(1760777233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358058601/2500000000 : ℝ)|^4525 ≤ (45442574793031/100000000000000 : ℝ)^3501
        have hw : |(1358058601/2500000000 : ℝ)|=(1358058601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647434349/5000000000 : ℝ)*x 0 + (543223437/1000000000 : ℝ)*x 1 + (-220097149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647434349/5000000000 : ℝ)^4525 ≤ (43962885716907/100000000000000 : ℝ)^3501 := by
    have hnat : (2647434349 : ℕ)^4525*100000000000000^3501 ≤ 43962885716907^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647434349 5000000000 43962885716907 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543223437/1000000000 : ℝ)^4525 ≤ (45442574425419/100000000000000 : ℝ)^3501 := by
    have hnat : (543223437 : ℕ)^4525*100000000000000^3501 ≤ 45442574425419^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543223437 1000000000 45442574425419 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220097149/1250000000 : ℝ)^4525 ≤ (1324317481281/12500000000000 : ℝ)^3501 := by
    have hnat : (220097149 : ℕ)^4525*12500000000000^3501 ≤ 1324317481281^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220097149 1250000000 1324317481281 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647434349/5000000000 : ℝ), (543223437/1000000000 : ℝ), (-220097149/1250000000 : ℝ)] ![(43962885716907/100000000000000 : ℝ), (45442574425419/100000000000000 : ℝ), (1324317481281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647434349/5000000000 : ℝ)|^4525 ≤ (43962885716907/100000000000000 : ℝ)^3501
        have hw : |(2647434349/5000000000 : ℝ)|=(2647434349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543223437/1000000000 : ℝ)|^4525 ≤ (45442574425419/100000000000000 : ℝ)^3501
        have hw : |(543223437/1000000000 : ℝ)|=(543223437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220097149/1250000000 : ℝ)|^4525 ≤ (1324317481281/12500000000000 : ℝ)^3501
        have hw : |(-220097149/1250000000 : ℝ)|=(220097149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s4_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268871827/10000000000 : ℝ)*x 0 + (2258724507/5000000000 : ℝ)*x 1 + (7875233/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268871827/10000000000 : ℝ)^4525 ≤ (33280066796423/100000000000000 : ℝ)^3501 := by
    have hnat : (4268871827 : ℕ)^4525*100000000000000^3501 ≤ 33280066796423^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268871827 10000000000 33280066796423 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258724507/5000000000 : ℝ)^4525 ≤ (35805828520741/100000000000000 : ℝ)^3501 := by
    have hnat : (2258724507 : ℕ)^4525*100000000000000^3501 ≤ 35805828520741^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258724507 5000000000 35805828520741 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7875233/19531250 : ℝ)^4525 ≤ (30914104666489/100000000000000 : ℝ)^3501 := by
    have hnat : (7875233 : ℕ)^4525*100000000000000^3501 ≤ 30914104666489^3501*19531250^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7875233 19531250 30914104666489 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268871827/10000000000 : ℝ), (2258724507/5000000000 : ℝ), (7875233/19531250 : ℝ)] ![(33280066796423/100000000000000 : ℝ), (35805828520741/100000000000000 : ℝ), (30914104666489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268871827/10000000000 : ℝ)|^4525 ≤ (33280066796423/100000000000000 : ℝ)^3501
        have hw : |(4268871827/10000000000 : ℝ)|=(4268871827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258724507/5000000000 : ℝ)|^4525 ≤ (35805828520741/100000000000000 : ℝ)^3501
        have hw : |(2258724507/5000000000 : ℝ)|=(2258724507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7875233/19531250 : ℝ)|^4525 ≤ (30914104666489/100000000000000 : ℝ)^3501
        have hw : |(7875233/19531250 : ℝ)|=(7875233/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15549/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2729/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15549/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15549/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15549/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15549/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15549/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15549/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5431/50000 : ℝ) ^ (4523/1024 : ℝ) ≤ (5515960045580511/100000000000000000000 : ℝ) := by
    have hpowers : (5431/50000 : ℝ)^4523 ≤ (5515960045580511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5431 : ℕ)^4523*100000000000000000000^1024 ≤ 5515960045580511^1024*50000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5431 50000 5515960045580511 100000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5431/50000 : ℝ)) (X := (5515960045580511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15549/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (3362529548100853/12500000000000000000 : ℝ) := by
    have hpowers : (15549/100000 : ℝ)^4523 ≤ (3362529548100853/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15549 : ℕ)^4523*12500000000000000000^1024 ≤ 3362529548100853^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15549 100000 3362529548100853 12500000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15549/100000 : ℝ)) (X := (3362529548100853/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005515960045580511/50000000000000000000 : ℝ) ≤ (10000249750257741/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (50005515960045580511/50000000000000000000 : ℝ)^1024 ≤ (10000249750257741/10000000000000000 : ℝ)^4523 := by
      have hnat : (50005515960045580511 : ℕ)^1024*10000000000000000^4523 ≤ 10000249750257741^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005515960045580511 50000000000000000000 10000249750257741 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000249750257741/10000000000000000 : ℝ)) (X := (50005515960045580511/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006483239286077467/20000000000000000000 : ℝ) ≤ (5000366902762023/5000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (20006483239286077467/20000000000000000000 : ℝ)^1024 ≤ (5000366902762023/5000000000000000 : ℝ)^4523 := by
      have hnat : (20006483239286077467 : ℕ)^1024*5000000000000000^4523 ≤ 5000366902762023^4523*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006483239286077467 20000000000000000000 5000366902762023 5000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000366902762023/5000000000000000 : ℝ)) (X := (20006483239286077467/20000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253362529548100853/6250000000000000000 : ℝ) ≤ (10001217860790351/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (6253362529548100853/6250000000000000000 : ℝ)^1024 ≤ (10001217860790351/10000000000000000 : ℝ)^4523 := by
      have hnat : (6253362529548100853 : ℕ)^1024*10000000000000000^4523 ≤ 10001217860790351^4523*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253362529548100853 6250000000000000000 10001217860790351 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001217860790351/10000000000000000 : ℝ)) (X := (6253362529548100853/6250000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5515960045580511/100000000000000000000 : ℝ) ≤ ((46860654962852822247/46870000000000000000 : ℝ)+2*(96811053261/93740000000000 : ℝ)*(5431/50000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (46860654962852822247/46870000000000000000 : ℝ)+2*(96811053261/93740000000000 : ℝ)*(5431/50000 : ℝ)=(10000249750257741/10000000000000000 : ℝ) by norm_num, show 1+2*(5515960045580511/100000000000000000000 : ℝ)=(50005515960045580511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3362529548100853/12500000000000000000 : ℝ)+(5515960045580511/100000000000000000000 : ℝ) ≤ ((46860654962852822247/46870000000000000000 : ℝ)+(96811053261/93740000000000 : ℝ)*((15549/100000 : ℝ)+(5431/50000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (46860654962852822247/46870000000000000000 : ℝ)+(96811053261/93740000000000 : ℝ)*((15549/100000 : ℝ)+(5431/50000 : ℝ))=(5000366902762023/5000000000000000 : ℝ) by norm_num, show 1+(3362529548100853/12500000000000000000 : ℝ)+(5515960045580511/100000000000000000000 : ℝ)=(20006483239286077467/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3362529548100853/12500000000000000000 : ℝ) ≤ ((46860654962852822247/46870000000000000000 : ℝ)+2*(96811053261/93740000000000 : ℝ)*(15549/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (46860654962852822247/46870000000000000000 : ℝ)+2*(96811053261/93740000000000 : ℝ)*(15549/100000 : ℝ)=(10001217860790351/10000000000000000 : ℝ) by norm_num, show 1+2*(3362529548100853/12500000000000000000 : ℝ)=(6253362529548100853/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46860654962852822247/46870000000000000000 : ℝ)*(X 1 0+X 2 0)+(96811053261/93740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (5431/50000 : ℝ)) (hi := (15549/100000 : ℝ)) (c := (46860654962852822247/46870000000000000000 : ℝ)) (alpha := (96811053261/93740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46860654962852822247/46870000000000000000 : ℝ)*(X 0 1+X 2 1)+(96811053261/93740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (5431/50000 : ℝ)) (hi := (15549/100000 : ℝ)) (c := (46860654962852822247/46870000000000000000 : ℝ)) (alpha := (96811053261/93740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46860654962852822247/46870000000000000000 : ℝ)*(X 0 2+X 1 2)+(96811053261/93740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (5431/50000 : ℝ)) (hi := (15549/100000 : ℝ)) (c := (46860654962852822247/46870000000000000000 : ℝ)) (alpha := (96811053261/93740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1865008193/10000000000 : ℝ)*X 0 0+(108667167/200000000 : ℝ)*X 0 1+(652173833/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337895159/2500000000 : ℝ)*X 1 0+(-19756213/100000000 : ℝ)*X 1 1+(5217389897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351580141/10000000000 : ℝ)*X 2 0+(5217390641/10000000000 : ℝ)*X 2 1+(-987810487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268805127/10000000000 : ℝ)*X 0 0+(4029566683/10000000000 : ℝ)*X 0 1+(2259991667/5000000000 : ℝ)*X 0 2+(4268805127/10000000000 : ℝ)*X 1 0+(4029566683/10000000000 : ℝ)*X 1 1+(2259991667/5000000000 : ℝ)*X 1 2+(4268805127/10000000000 : ℝ)*X 2 0+(4029566683/10000000000 : ℝ)*X 2 1+(2259991667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-37300751/200000000 : ℝ)*X 0 0+(521850623/1000000000 : ℝ)*X 0 1+(5432234399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294868633/10000000000 : ℝ)*X 1 0+(-1760777233/10000000000 : ℝ)*X 1 1+(1358058601/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647434349/5000000000 : ℝ)*X 2 0+(543223437/1000000000 : ℝ)*X 2 1+(-220097149/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268871827/10000000000 : ℝ)*X 0 0+(2258724507/5000000000 : ℝ)*X 0 1+(7875233/19531250 : ℝ)*X 0 2+(4268871827/10000000000 : ℝ)*X 1 0+(2258724507/5000000000 : ℝ)*X 1 1+(7875233/19531250 : ℝ)*X 1 2+(4268871827/10000000000 : ℝ)*X 2 0+(2258724507/5000000000 : ℝ)*X 2 1+(7875233/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21528512990705614364703/2343500000000000000000000000 : ℝ) := by norm_num
    linear_combination (363456827/20000000000000 : ℝ)*(base19) + (620864397/50000000000000 : ℝ)*(base23) + (15762033/20000000000000 : ℝ)*(lower2) + (19648529/50000000000000 : ℝ)*(upper3) + (175512699/100000000000000 : ℝ)*(upper5) + (3334734707283397/100000000000000 : ℝ)*(major0) + (3334734707283397/100000000000000 : ℝ)*(major1) + (3334734707283397/100000000000000 : ℝ)*(major2) + (4630341098484203/100000000000000 : ℝ)*(sp0) + (926072275174837/20000000000000 : ℝ)*(sp1) + (2315180975714763/50000000000000 : ℝ)*(sp2) + (407819029973827/20000000000000 : ℝ)*(sp3) + (22094674117/100000000000000 : ℝ)*(sp4) + (1076532337/10000000000000 : ℝ)*(sp7) + (254888239399063/12500000000000 : ℝ)*(f.failure) + (57879539914479/1250000000000 : ℝ)*(f.sum) + (3113063470741/937400000000000000000000000 : ℝ)*base66 + (26744955054688833059/4687000000000000000000000000000000 : ℝ)*base67 + (19041385891691166941/4687000000000000000000000000000000 : ℝ)*base70 + (15575114834538833059/4687000000000000000000000000000000 : ℝ)*base71 + (1893354777689/2343500000000000000000000000 : ℝ)*base74 + (37864740993581166941/4687000000000000000000000000000000 : ℝ)*base76 + (6743112455916833059/4687000000000000000000000000000000 : ℝ)*base77 + (17435045374833166941/4687000000000000000000000000000000 : ℝ)*base80 + (4592919677573/937400000000000000000000000 : ℝ)*base82 + (16402031/1250000000000000000000 : ℝ)*base90 + (16402031/1250000000000000000000 : ℝ)*base92 + (16402031/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58570787014384503729/10750000000000000000000000 : ℝ) := by norm_num
    linear_combination (846809449/100000000000000 : ℝ)*(base19) + (523148023/50000000000000 : ℝ)*(base23) + (100783991/100000000000000 : ℝ)*(upper3) + (63349291/100000000000000 : ℝ)*(lower4) + (139560489/100000000000000 : ℝ)*(upper5) + (336964766074923/10000000000000 : ℝ)*(major0) + (336964766074923/10000000000000 : ℝ)*(major1) + (336964766074923/10000000000000 : ℝ)*(major2) + (53686853/400000000000 : ℝ)*(sp1) + (3878450383/25000000000000 : ℝ)*(sp2) + (1169710209208697/25000000000000 : ℝ)*(sp4) + (4678826568312089/100000000000000 : ℝ)*(sp5) + (467882427673721/10000000000000 : ℝ)*(sp6) + (1030227151524413/50000000000000 : ℝ)*(sp7) + (1030227151524413/50000000000000 : ℝ)*(f.failure) + (1169710209208697/25000000000000 : ℝ)*(f.sum) + (7263609871/10750000000000000000000000 : ℝ)*base65 + (23671805384220991/4300000000000000000000000000000 : ℝ)*base68 + (10238313431420991/4300000000000000000000000000000 : ℝ)*base70 + (7710155185279009/4300000000000000000000000000000 : ℝ)*base71 + (1687426891/43000000000000000000000000 : ℝ)*base74 + (9531053554379009/4300000000000000000000000000000 : ℝ)*base75 + (5895566988779009/4300000000000000000000000000000 : ℝ)*base77 + (16574399413820991/4300000000000000000000000000000 : ℝ)*base80 + (61926012837/21500000000000000000000000 : ℝ)*base82 + (23645019/5000000000000000000000 : ℝ)*base89 + (23645019/5000000000000000000000 : ℝ)*base91 + (23645019/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1514_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15549/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2729/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1514_s5_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865061527/10000000000 : ℝ)*x 0 + (271650691/500000000 : ℝ)*x 1 + (326106239/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865061527/10000000000 : ℝ)^4525 ≤ (1426559138149/12500000000000 : ℝ)^3501 := by
    have hnat : (1865061527 : ℕ)^4525*12500000000000^3501 ≤ 1426559138149^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865061527 10000000000 1426559138149 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271650691/500000000 : ℝ)^4525 ≤ (45451002110039/100000000000000 : ℝ)^3501 := by
    have hnat : (271650691 : ℕ)^4525*100000000000000^3501 ≤ 45451002110039^3501*500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271650691 500000000 45451002110039 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326106239/625000000 : ℝ)^4525 ≤ (43136524775713/100000000000000 : ℝ)^3501 := by
    have hnat : (326106239 : ℕ)^4525*100000000000000^3501 ≤ 43136524775713^3501*625000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326106239 625000000 43136524775713 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865061527/10000000000 : ℝ), (271650691/500000000 : ℝ), (326106239/625000000 : ℝ)] ![(1426559138149/12500000000000 : ℝ), (45451002110039/100000000000000 : ℝ), (43136524775713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865061527/10000000000 : ℝ)|^4525 ≤ (1426559138149/12500000000000 : ℝ)^3501
        have hw : |(-1865061527/10000000000 : ℝ)|=(1865061527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271650691/500000000 : ℝ)|^4525 ≤ (45451002110039/100000000000000 : ℝ)^3501
        have hw : |(271650691/500000000 : ℝ)|=(271650691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326106239/625000000 : ℝ)|^4525 ≤ (43136524775713/100000000000000 : ℝ)^3501
        have hw : |(326106239/625000000 : ℝ)|=(326106239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133787239/250000000 : ℝ)*x 0 + (-246916419/1250000000 : ℝ)*x 1 + (2608849949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133787239/250000000 : ℝ)^4525 ≤ (11142864052377/25000000000000 : ℝ)^3501 := by
    have hnat : (133787239 : ℕ)^4525*25000000000000^3501 ≤ 11142864052377^3501*250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133787239 250000000 11142864052377 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246916419/1250000000 : ℝ)^4525 ≤ (2458403640347/20000000000000 : ℝ)^3501 := by
    have hnat : (246916419 : ℕ)^4525*20000000000000^3501 ≤ 2458403640347^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246916419 1250000000 2458403640347 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608849949/5000000000 : ℝ)^4525 ≤ (8627305113287/20000000000000 : ℝ)^3501 := by
    have hnat : (2608849949 : ℕ)^4525*20000000000000^3501 ≤ 8627305113287^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608849949 5000000000 8627305113287 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133787239/250000000 : ℝ), (-246916419/1250000000 : ℝ), (2608849949/5000000000 : ℝ)] ![(11142864052377/25000000000000 : ℝ), (2458403640347/20000000000000 : ℝ), (8627305113287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133787239/250000000 : ℝ)|^4525 ≤ (11142864052377/25000000000000 : ℝ)^3501
        have hw : |(133787239/250000000 : ℝ)|=(133787239/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246916419/1250000000 : ℝ)|^4525 ≤ (2458403640347/20000000000000 : ℝ)^3501
        have hw : |(-246916419/1250000000 : ℝ)|=(246916419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608849949/5000000000 : ℝ)|^4525 ≤ (8627305113287/20000000000000 : ℝ)^3501
        have hw : |(2608849949/5000000000 : ℝ)|=(2608849949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214059583/400000000 : ℝ)*x 0 + (652212483/1250000000 : ℝ)*x 1 + (-1975331379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214059583/400000000 : ℝ)^4525 ≤ (44571456370981/100000000000000 : ℝ)^3501 := by
    have hnat : (214059583 : ℕ)^4525*100000000000000^3501 ≤ 44571456370981^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214059583 400000000 44571456370981 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652212483/1250000000 : ℝ)^4525 ≤ (4313652520313/10000000000000 : ℝ)^3501 := by
    have hnat : (652212483 : ℕ)^4525*10000000000000^3501 ≤ 4313652520313^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652212483 1250000000 4313652520313 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975331379/10000000000 : ℝ)^4525 ≤ (3073004604723/25000000000000 : ℝ)^3501 := by
    have hnat : (1975331379 : ℕ)^4525*25000000000000^3501 ≤ 3073004604723^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975331379 10000000000 3073004604723 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214059583/400000000 : ℝ), (652212483/1250000000 : ℝ), (-1975331379/10000000000 : ℝ)] ![(44571456370981/100000000000000 : ℝ), (4313652520313/10000000000000 : ℝ), (3073004604723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214059583/400000000 : ℝ)|^4525 ≤ (44571456370981/100000000000000 : ℝ)^3501
        have hw : |(214059583/400000000 : ℝ)|=(214059583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652212483/1250000000 : ℝ)|^4525 ≤ (4313652520313/10000000000000 : ℝ)^3501
        have hw : |(652212483/1250000000 : ℝ)|=(652212483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975331379/10000000000 : ℝ)|^4525 ≤ (3073004604723/25000000000000 : ℝ)^3501
        have hw : |(-1975331379/10000000000 : ℝ)|=(1975331379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268837829/10000000000 : ℝ)*x 0 + (4030305701/10000000000 : ℝ)*x 1 + (1129809133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268837829/10000000000 : ℝ)^4525 ≤ (33279724225569/100000000000000 : ℝ)^3501 := by
    have hnat : (4268837829 : ℕ)^4525*100000000000000^3501 ≤ 33279724225569^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268837829 10000000000 33279724225569 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030305701/10000000000 : ℝ)^4525 ≤ (15448067055301/50000000000000 : ℝ)^3501 := by
    have hnat : (4030305701 : ℕ)^4525*50000000000000^3501 ≤ 15448067055301^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030305701 10000000000 15448067055301 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129809133/2500000000 : ℝ)^4525 ≤ (7164828329427/20000000000000 : ℝ)^3501 := by
    have hnat : (1129809133 : ℕ)^4525*20000000000000^3501 ≤ 7164828329427^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129809133 2500000000 7164828329427 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268837829/10000000000 : ℝ), (4030305701/10000000000 : ℝ), (1129809133/2500000000 : ℝ)] ![(33279724225569/100000000000000 : ℝ), (15448067055301/50000000000000 : ℝ), (7164828329427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268837829/10000000000 : ℝ)|^4525 ≤ (33279724225569/100000000000000 : ℝ)^3501
        have hw : |(4268837829/10000000000 : ℝ)|=(4268837829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030305701/10000000000 : ℝ)|^4525 ≤ (15448067055301/50000000000000 : ℝ)^3501
        have hw : |(4030305701/10000000000 : ℝ)|=(4030305701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129809133/2500000000 : ℝ)|^4525 ≤ (7164828329427/20000000000000 : ℝ)^3501
        have hw : |(1129809133/2500000000 : ℝ)|=(1129809133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-466272589/2500000000 : ℝ)*x 0 + (2609404519/5000000000 : ℝ)*x 1 + (5431896493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466272589/2500000000 : ℝ)^4525 ≤ (5706350554903/50000000000000 : ℝ)^3501 := by
    have hnat : (466272589 : ℕ)^4525*50000000000000^3501 ≤ 5706350554903^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466272589 2500000000 5706350554903 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609404519/5000000000 : ℝ)^4525 ≤ (5393547198409/12500000000000 : ℝ)^3501 := by
    have hnat : (2609404519 : ℕ)^4525*12500000000000^3501 ≤ 5393547198409^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609404519 5000000000 5393547198409 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431896493/10000000000 : ℝ)^4525 ≤ (45438921291611/100000000000000 : ℝ)^3501 := by
    have hnat : (5431896493 : ℕ)^4525*100000000000000^3501 ≤ 45438921291611^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431896493 10000000000 45438921291611 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466272589/2500000000 : ℝ), (2609404519/5000000000 : ℝ), (5431896493/10000000000 : ℝ)] ![(5706350554903/50000000000000 : ℝ), (5393547198409/12500000000000 : ℝ), (45438921291611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466272589/2500000000 : ℝ)|^4525 ≤ (5706350554903/50000000000000 : ℝ)^3501
        have hw : |(-466272589/2500000000 : ℝ)|=(466272589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609404519/5000000000 : ℝ)|^4525 ≤ (5393547198409/12500000000000 : ℝ)^3501
        have hw : |(2609404519/5000000000 : ℝ)|=(2609404519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431896493/10000000000 : ℝ)|^4525 ≤ (45438921291611/100000000000000 : ℝ)^3501
        have hw : |(5431896493/10000000000 : ℝ)|=(5431896493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294949997/10000000000 : ℝ)*x 0 + (-1761134719/10000000000 : ℝ)*x 1 + (5431896507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294949997/10000000000 : ℝ)^4525 ≤ (21981879086569/50000000000000 : ℝ)^3501 := by
    have hnat : (5294949997 : ℕ)^4525*50000000000000^3501 ≤ 21981879086569^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294949997 10000000000 21981879086569 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761134719/10000000000 : ℝ)^4525 ≤ (1059732036951/10000000000000 : ℝ)^3501 := by
    have hnat : (1761134719 : ℕ)^4525*10000000000000^3501 ≤ 1059732036951^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761134719 10000000000 1059732036951 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431896507/10000000000 : ℝ)^4525 ≤ (22719460721489/50000000000000 : ℝ)^3501 := by
    have hnat : (5431896507 : ℕ)^4525*50000000000000^3501 ≤ 22719460721489^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431896507 10000000000 22719460721489 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294949997/10000000000 : ℝ), (-1761134719/10000000000 : ℝ), (5431896507/10000000000 : ℝ)] ![(21981879086569/50000000000000 : ℝ), (1059732036951/10000000000000 : ℝ), (22719460721489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294949997/10000000000 : ℝ)|^4525 ≤ (21981879086569/50000000000000 : ℝ)^3501
        have hw : |(5294949997/10000000000 : ℝ)|=(5294949997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761134719/10000000000 : ℝ)|^4525 ≤ (1059732036951/10000000000000 : ℝ)^3501
        have hw : |(-1761134719/10000000000 : ℝ)|=(1761134719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431896507/10000000000 : ℝ)|^4525 ≤ (22719460721489/50000000000000 : ℝ)^3501
        have hw : |(5431896507/10000000000 : ℝ)|=(5431896507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058989997/2000000000 : ℝ)*x 0 + (1357974127/2500000000 : ℝ)*x 1 + (-880567367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058989997/2000000000 : ℝ)^4525 ≤ (1099093951109/2500000000000 : ℝ)^3501 := by
    have hnat : (1058989997 : ℕ)^4525*2500000000000^3501 ≤ 1099093951109^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058989997 2000000000 1099093951109 2500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357974127/2500000000 : ℝ)^4525 ≤ (4543892145379/10000000000000 : ℝ)^3501 := by
    have hnat : (1357974127 : ℕ)^4525*10000000000000^3501 ≤ 4543892145379^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357974127 2500000000 4543892145379 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880567367/5000000000 : ℝ)^4525 ≤ (10597320486169/100000000000000 : ℝ)^3501 := by
    have hnat : (880567367 : ℕ)^4525*100000000000000^3501 ≤ 10597320486169^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880567367 5000000000 10597320486169 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058989997/2000000000 : ℝ), (1357974127/2500000000 : ℝ), (-880567367/5000000000 : ℝ)] ![(1099093951109/2500000000000 : ℝ), (4543892145379/10000000000000 : ℝ), (10597320486169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058989997/2000000000 : ℝ)|^4525 ≤ (1099093951109/2500000000000 : ℝ)^3501
        have hw : |(1058989997/2000000000 : ℝ)|=(1058989997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357974127/2500000000 : ℝ)|^4525 ≤ (4543892145379/10000000000000 : ℝ)^3501
        have hw : |(1357974127/2500000000 : ℝ)|=(1357974127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880567367/5000000000 : ℝ)|^4525 ≤ (10597320486169/100000000000000 : ℝ)^3501
        have hw : |(-880567367/5000000000 : ℝ)|=(880567367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s5_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533612927/1250000000 : ℝ)*x 0 + (45167179/100000000 : ℝ)*x 1 + (2016421483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533612927/1250000000 : ℝ)^4525 ≤ (8320096273603/25000000000000 : ℝ)^3501 := by
    have hnat : (533612927 : ℕ)^4525*25000000000000^3501 ≤ 8320096273603^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533612927 1250000000 8320096273603 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45167179/100000000 : ℝ)^4525 ≤ (17899169433317/50000000000000 : ℝ)^3501 := by
    have hnat : (45167179 : ℕ)^4525*50000000000000^3501 ≤ 17899169433317^3501*100000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45167179 100000000 17899169433317 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016421483/5000000000 : ℝ)^4525 ≤ (3865159503757/12500000000000 : ℝ)^3501 := by
    have hnat : (2016421483 : ℕ)^4525*12500000000000^3501 ≤ 3865159503757^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016421483 5000000000 3865159503757 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533612927/1250000000 : ℝ), (45167179/100000000 : ℝ), (2016421483/5000000000 : ℝ)] ![(8320096273603/25000000000000 : ℝ), (17899169433317/50000000000000 : ℝ), (3865159503757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533612927/1250000000 : ℝ)|^4525 ≤ (8320096273603/25000000000000 : ℝ)^3501
        have hw : |(533612927/1250000000 : ℝ)|=(533612927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45167179/100000000 : ℝ)|^4525 ≤ (17899169433317/50000000000000 : ℝ)^3501
        have hw : |(45167179/100000000 : ℝ)|=(45167179/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016421483/5000000000 : ℝ)|^4525 ≤ (3865159503757/12500000000000 : ℝ)^3501
        have hw : |(2016421483/5000000000 : ℝ)|=(2016421483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2729/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10923/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2729/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2729/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2729/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2729/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2729/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2729/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2729/25000 : ℝ) ^ (4523/1024 : ℝ) ≤ (140952934717153/2500000000000000000 : ℝ) := by
    have hpowers : (2729/25000 : ℝ)^4523 ≤ (140952934717153/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2729 : ℕ)^4523*2500000000000000000^1024 ≤ 140952934717153^1024*25000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2729 25000 140952934717153 2500000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2729/25000 : ℝ)) (X := (140952934717153/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4523/1024 : ℝ) ≤ (1322615001519063/5000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4523 ≤ (1322615001519063/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4523*5000000000000000000^1024 ≤ 1322615001519063^1024*10000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 1322615001519063 5000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (1322615001519063/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250140952934717153/1250000000000000000 : ℝ) ≤ (156253988766033/156250000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (1250140952934717153/1250000000000000000 : ℝ)^1024 ≤ (156253988766033/156250000000000 : ℝ)^4523 := by
      have hnat : (1250140952934717153 : ℕ)^1024*156250000000000^4523 ≤ 156253988766033^4523*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250140952934717153 1250000000000000000 156253988766033 156250000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156253988766033/156250000000000 : ℝ)) (X := (1250140952934717153/1250000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001604520870953369/5000000000000000000 : ℝ) ≤ (10000726431778861/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (5001604520870953369/5000000000000000000 : ℝ)^1024 ≤ (10000726431778861/10000000000000000 : ℝ)^4523 := by
      have hnat : (5001604520870953369 : ℕ)^1024*10000000000000000^4523 ≤ 10000726431778861^4523*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001604520870953369 5000000000000000000 10000726431778861 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000726431778861/10000000000000000 : ℝ)) (X := (5001604520870953369/5000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501322615001519063/2500000000000000000 : ℝ) ≤ (1000119758253161/1000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (2501322615001519063/2500000000000000000 : ℝ)^1024 ≤ (1000119758253161/1000000000000000 : ℝ)^4523 := by
      have hnat : (2501322615001519063 : ℕ)^1024*1000000000000000^4523 ≤ 1000119758253161^4523*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501322615001519063 2500000000000000000 1000119758253161 1000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000119758253161/1000000000000000 : ℝ)) (X := (2501322615001519063/2500000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(140952934717153/2500000000000000000 : ℝ) ≤ ((1143272037304485503/1143500000000000000 : ℝ)+2*(471150752749/457400000000000 : ℝ)*(2729/25000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (1143272037304485503/1143500000000000000 : ℝ)+2*(471150752749/457400000000000 : ℝ)*(2729/25000 : ℝ)=(156253988766033/156250000000000 : ℝ) by norm_num, show 1+2*(140952934717153/2500000000000000000 : ℝ)=(1250140952934717153/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1322615001519063/5000000000000000000 : ℝ)+(140952934717153/2500000000000000000 : ℝ) ≤ ((1143272037304485503/1143500000000000000 : ℝ)+(471150752749/457400000000000 : ℝ)*((1549/10000 : ℝ)+(2729/25000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (1143272037304485503/1143500000000000000 : ℝ)+(471150752749/457400000000000 : ℝ)*((1549/10000 : ℝ)+(2729/25000 : ℝ))=(10000726431778861/10000000000000000 : ℝ) by norm_num, show 1+(1322615001519063/5000000000000000000 : ℝ)+(140952934717153/2500000000000000000 : ℝ)=(5001604520870953369/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1322615001519063/5000000000000000000 : ℝ) ≤ ((1143272037304485503/1143500000000000000 : ℝ)+2*(471150752749/457400000000000 : ℝ)*(1549/10000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (1143272037304485503/1143500000000000000 : ℝ)+2*(471150752749/457400000000000 : ℝ)*(1549/10000 : ℝ)=(1000119758253161/1000000000000000 : ℝ) by norm_num, show 1+2*(1322615001519063/5000000000000000000 : ℝ)=(2501322615001519063/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1143272037304485503/1143500000000000000 : ℝ)*(X 1 0+X 2 0)+(471150752749/457400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2729/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1143272037304485503/1143500000000000000 : ℝ)) (alpha := (471150752749/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1143272037304485503/1143500000000000000 : ℝ)*(X 0 1+X 2 1)+(471150752749/457400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2729/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1143272037304485503/1143500000000000000 : ℝ)) (alpha := (471150752749/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1143272037304485503/1143500000000000000 : ℝ)*(X 0 2+X 1 2)+(471150752749/457400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2729/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1143272037304485503/1143500000000000000 : ℝ)) (alpha := (471150752749/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1865061527/10000000000 : ℝ)*X 0 0+(271650691/500000000 : ℝ)*X 0 1+(326106239/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133787239/250000000 : ℝ)*X 1 0+(-246916419/1250000000 : ℝ)*X 1 1+(2608849949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214059583/400000000 : ℝ)*X 2 0+(652212483/1250000000 : ℝ)*X 2 1+(-1975331379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268837829/10000000000 : ℝ)*X 0 0+(4030305701/10000000000 : ℝ)*X 0 1+(1129809133/2500000000 : ℝ)*X 0 2+(4268837829/10000000000 : ℝ)*X 1 0+(4030305701/10000000000 : ℝ)*X 1 1+(1129809133/2500000000 : ℝ)*X 1 2+(4268837829/10000000000 : ℝ)*X 2 0+(4030305701/10000000000 : ℝ)*X 2 1+(1129809133/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-466272589/2500000000 : ℝ)*X 0 0+(2609404519/5000000000 : ℝ)*X 0 1+(5431896493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294949997/10000000000 : ℝ)*X 1 0+(-1761134719/10000000000 : ℝ)*X 1 1+(5431896507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058989997/2000000000 : ℝ)*X 2 0+(1357974127/2500000000 : ℝ)*X 2 1+(-880567367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533612927/1250000000 : ℝ)*X 0 0+(45167179/100000000 : ℝ)*X 0 1+(2016421483/5000000000 : ℝ)*X 0 2+(533612927/1250000000 : ℝ)*X 1 0+(45167179/100000000 : ℝ)*X 1 1+(2016421483/5000000000 : ℝ)*X 1 2+(533612927/1250000000 : ℝ)*X 2 0+(45167179/100000000 : ℝ)*X 2 1+(2016421483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76176471022835963403175443/14293750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228098809/25000000000000 : ℝ)*(base19) + (878131767/100000000000000 : ℝ)*(base23) + (1012107/4000000000000 : ℝ)*(lower2) + (7249517/5000000000000 : ℝ)*(upper3) + (87336983/100000000000000 : ℝ)*(upper5) + (1672425971965423/50000000000000 : ℝ)*(major0) + (1672425971965423/50000000000000 : ℝ)*(major1) + (1672425971965423/50000000000000 : ℝ)*(major2) + (4644396154485467/100000000000000 : ℝ)*(sp0) + (928882089670631/20000000000000 : ℝ)*(sp1) + (4644410482616623/100000000000000 : ℝ)*(sp2) + (2045285285862597/100000000000000 : ℝ)*(sp3) + (15206262923/100000000000000 : ℝ)*(sp4) + (7063605521/100000000000000 : ℝ)*(sp7) + (1022646174734059/50000000000000 : ℝ)*(f.failure) + (4644411360748391/100000000000000 : ℝ)*(f.sum) + (9814439458293/11435000000000000000000000000 : ℝ)*base66 + (383167582691405269/57175000000000000000000000000000 : ℝ)*base67 + (160793863452355269/57175000000000000000000000000000 : ℝ)*base69 + (551230062518755269/57175000000000000000000000000000 : ℝ)*base71 + (6508840749567/2858750000000000000000000000 : ℝ)*base74 + (414123136583669731/57175000000000000000000000000000 : ℝ)*base76 + (635240524694380269/57175000000000000000000000000000 : ℝ)*base77 + (712816491215255269/57175000000000000000000000000000 : ℝ)*base79 + (10018870991607/2858750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (16953283/5000000000000000000000 : ℝ)*base90 + (16953283/5000000000000000000000 : ℝ)*base92 + (16953283/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177164873719679513849127/22870000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1143640773/100000000000000 : ℝ)*(base19) + (1270740449/100000000000000 : ℝ)*(base23) + (198439411/50000000000000 : ℝ)*(lower1) + (66059079/50000000000000 : ℝ)*(upper3) + (65593663/100000000000000 : ℝ)*(lower4) + (145284439/100000000000000 : ℝ)*(upper5) + (3379765318801091/100000000000000 : ℝ)*(major0) + (3379765318801091/100000000000000 : ℝ)*(major1) + (3379765318801091/100000000000000 : ℝ)*(major2) + (324394369/25000000000000 : ℝ)*(sp2) + (4692889384379399/100000000000000 : ℝ)*(sp4) + (2346444120369313/50000000000000 : ℝ)*(sp5) + (2346443408030737/50000000000000 : ℝ)*(sp6) + (2066640995002577/100000000000000 : ℝ)*(sp7) + (2066640995002577/100000000000000 : ℝ)*(f.failure) + (4692889384379399/100000000000000 : ℝ)*(f.sum) + (51538731766401/22870000000000000000000000000 : ℝ)*base66 + (1859279864243281273/114350000000000000000000000000000 : ℝ)*base67 + (413247385354168727/114350000000000000000000000000000 : ℝ)*base70 + (4359708342613081273/114350000000000000000000000000000 : ℝ)*base71 + (48450028902061/22870000000000000000000000000 : ℝ)*base74 + (7418309137390418727/114350000000000000000000000000000 : ℝ)*base76 + (450733892002718727/114350000000000000000000000000000 : ℝ)*base78 + (90698408564381273/114350000000000000000000000000000 : ℝ)*base79 + (129702837611219/22870000000000000000000000000 : ℝ)*base81 + (25165351/10000000000000000000000 : ℝ)*base89 + (25165351/10000000000000000000000 : ℝ)*base91 + (25165351/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1514_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2729/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1514_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1514_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1514_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1514_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
