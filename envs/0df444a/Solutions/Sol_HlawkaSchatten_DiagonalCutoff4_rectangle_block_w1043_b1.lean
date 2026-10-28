-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:48:36.334027+00:00
-- url     : https://prove2.me/submissions/45207bca-edb9-4c3f-8567-d1aa90302b38

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
theorem support_rectangle_w1043_s3_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210076871/10000000000 : ℝ)*x 0 + (272013799/500000000 : ℝ)*x 1 + (5221814713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210076871/10000000000 : ℝ)^2059 ≤ (13410049405529/100000000000000 : ℝ)^1547 := by
    have hnat : (2210076871 : ℕ)^2059*100000000000000^1547 ≤ 13410049405529^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210076871 10000000000 13410049405529 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272013799/500000000 : ℝ)^2059 ≤ (2779721066721/6250000000000 : ℝ)^1547 := by
    have hnat : (272013799 : ℕ)^2059*6250000000000^1547 ≤ 2779721066721^1547*500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272013799 500000000 2779721066721 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221814713/10000000000 : ℝ)^2059 ≤ (42114413510987/100000000000000 : ℝ)^1547 := by
    have hnat : (5221814713 : ℕ)^2059*100000000000000^1547 ≤ 42114413510987^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221814713 10000000000 42114413510987 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210076871/10000000000 : ℝ), (272013799/500000000 : ℝ), (5221814713/10000000000 : ℝ)] ![(13410049405529/100000000000000 : ℝ), (2779721066721/6250000000000 : ℝ), (42114413510987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210076871/10000000000 : ℝ)|^2059 ≤ (13410049405529/100000000000000 : ℝ)^1547
        have hw : |(-2210076871/10000000000 : ℝ)|=(2210076871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272013799/500000000 : ℝ)|^2059 ≤ (2779721066721/6250000000000 : ℝ)^1547
        have hw : |(272013799/500000000 : ℝ)|=(272013799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221814713/10000000000 : ℝ)|^2059 ≤ (42114413510987/100000000000000 : ℝ)^1547
        have hw : |(5221814713/10000000000 : ℝ)|=(5221814713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1071258653/2000000000 : ℝ)*x 0 + (-2322012523/10000000000 : ℝ)*x 1 + (1305453639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071258653/2000000000 : ℝ)^2059 ≤ (21782034454467/50000000000000 : ℝ)^1547 := by
    have hnat : (1071258653 : ℕ)^2059*50000000000000^1547 ≤ 21782034454467^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071258653 2000000000 21782034454467 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2322012523/10000000000 : ℝ)^2059 ≤ (14321519255621/100000000000000 : ℝ)^1547 := by
    have hnat : (2322012523 : ℕ)^2059*100000000000000^1547 ≤ 14321519255621^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322012523 10000000000 14321519255621 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305453639/2500000000 : ℝ)^2059 ≤ (1316075369553/3125000000000 : ℝ)^1547 := by
    have hnat : (1305453639 : ℕ)^2059*3125000000000^1547 ≤ 1316075369553^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305453639 2500000000 1316075369553 3125000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071258653/2000000000 : ℝ), (-2322012523/10000000000 : ℝ), (1305453639/2500000000 : ℝ)] ![(21782034454467/50000000000000 : ℝ), (14321519255621/100000000000000 : ℝ), (1316075369553/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071258653/2000000000 : ℝ)|^2059 ≤ (21782034454467/50000000000000 : ℝ)^1547
        have hw : |(1071258653/2000000000 : ℝ)|=(1071258653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2322012523/10000000000 : ℝ)|^2059 ≤ (14321519255621/100000000000000 : ℝ)^1547
        have hw : |(-2322012523/10000000000 : ℝ)|=(2322012523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305453639/2500000000 : ℝ)|^2059 ≤ (1316075369553/3125000000000 : ℝ)^1547
        have hw : |(1305453639/2500000000 : ℝ)|=(1305453639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5356293163/10000000000 : ℝ)*x 0 + (5221814409/10000000000 : ℝ)*x 1 + (-2322012849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356293163/10000000000 : ℝ)^2059 ≤ (43564067804779/100000000000000 : ℝ)^1547 := by
    have hnat : (5356293163 : ℕ)^2059*100000000000000^1547 ≤ 43564067804779^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356293163 10000000000 43564067804779 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221814409/10000000000 : ℝ)^2059 ≤ (10528602561937/25000000000000 : ℝ)^1547 := by
    have hnat : (5221814409 : ℕ)^2059*25000000000000^1547 ≤ 10528602561937^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221814409 10000000000 10528602561937 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2322012849/10000000000 : ℝ)^2059 ≤ (14321521931757/100000000000000 : ℝ)^1547 := by
    have hnat : (2322012849 : ℕ)^2059*100000000000000^1547 ≤ 14321521931757^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322012849 10000000000 14321521931757 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356293163/10000000000 : ℝ), (5221814409/10000000000 : ℝ), (-2322012849/10000000000 : ℝ)] ![(43564067804779/100000000000000 : ℝ), (10528602561937/25000000000000 : ℝ), (14321521931757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356293163/10000000000 : ℝ)|^2059 ≤ (43564067804779/100000000000000 : ℝ)^1547
        have hw : |(5356293163/10000000000 : ℝ)|=(5356293163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221814409/10000000000 : ℝ)|^2059 ≤ (10528602561937/25000000000000 : ℝ)^1547
        have hw : |(5221814409/10000000000 : ℝ)|=(5221814409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2322012849/10000000000 : ℝ)|^2059 ≤ (14321521931757/100000000000000 : ℝ)^1547
        have hw : |(-2322012849/10000000000 : ℝ)|=(2322012849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (273488683/625000000 : ℝ)*x 0 + (2083997837/5000000000 : ℝ)*x 1 + (4594196519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273488683/625000000 : ℝ)^2059 ≤ (3328612273873/10000000000000 : ℝ)^1547 := by
    have hnat : (273488683 : ℕ)^2059*10000000000000^1547 ≤ 3328612273873^1547*625000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273488683 625000000 3328612273873 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083997837/5000000000 : ℝ)^2059 ≤ (7799687362807/25000000000000 : ℝ)^1547 := by
    have hnat : (2083997837 : ℕ)^2059*25000000000000^1547 ≤ 7799687362807^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083997837 5000000000 7799687362807 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4594196519/10000000000 : ℝ)^2059 ≤ (35515127784877/100000000000000 : ℝ)^1547 := by
    have hnat : (4594196519 : ℕ)^2059*100000000000000^1547 ≤ 35515127784877^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594196519 10000000000 35515127784877 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273488683/625000000 : ℝ), (2083997837/5000000000 : ℝ), (4594196519/10000000000 : ℝ)] ![(3328612273873/10000000000000 : ℝ), (7799687362807/25000000000000 : ℝ), (35515127784877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273488683/625000000 : ℝ)|^2059 ≤ (3328612273873/10000000000000 : ℝ)^1547
        have hw : |(273488683/625000000 : ℝ)|=(273488683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083997837/5000000000 : ℝ)|^2059 ≤ (7799687362807/25000000000000 : ℝ)^1547
        have hw : |(2083997837/5000000000 : ℝ)|=(2083997837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4594196519/10000000000 : ℝ)|^2059 ≤ (35515127784877/100000000000000 : ℝ)^1547
        have hw : |(4594196519/10000000000 : ℝ)|=(4594196519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210100629/10000000000 : ℝ)*x 0 + (81605077/156250000 : ℝ)*x 1 + (5439360343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210100629/10000000000 : ℝ)^2059 ≤ (6705120636131/50000000000000 : ℝ)^1547 := by
    have hnat : (2210100629 : ℕ)^2059*50000000000000^1547 ≤ 6705120636131^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210100629 10000000000 6705120636131 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81605077/156250000 : ℝ)^2059 ≤ (42124184349763/100000000000000 : ℝ)^1547 := by
    have hnat : (81605077 : ℕ)^2059*100000000000000^1547 ≤ 42124184349763^1547*156250000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81605077 156250000 42124184349763 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439360343/10000000000 : ℝ)^2059 ≤ (44465574356367/100000000000000 : ℝ)^1547 := by
    have hnat : (5439360343 : ℕ)^2059*100000000000000^1547 ≤ 44465574356367^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439360343 10000000000 44465574356367 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210100629/10000000000 : ℝ), (81605077/156250000 : ℝ), (5439360343/10000000000 : ℝ)] ![(6705120636131/50000000000000 : ℝ), (42124184349763/100000000000000 : ℝ), (44465574356367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210100629/10000000000 : ℝ)|^2059 ≤ (6705120636131/50000000000000 : ℝ)^1547
        have hw : |(-2210100629/10000000000 : ℝ)|=(2210100629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81605077/156250000 : ℝ)|^2059 ≤ (42124184349763/100000000000000 : ℝ)^1547
        have hw : |(81605077/156250000 : ℝ)|=(81605077/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439360343/10000000000 : ℝ)|^2059 ≤ (44465574356367/100000000000000 : ℝ)^1547
        have hw : |(5439360343/10000000000 : ℝ)|=(5439360343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650681341/5000000000 : ℝ)*x 0 + (-2104467349/10000000000 : ℝ)*x 1 + (5439359701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650681341/5000000000 : ℝ)^2059 ≤ (10742613438199/25000000000000 : ℝ)^1547 := by
    have hnat : (2650681341 : ℕ)^2059*25000000000000^1547 ≤ 10742613438199^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650681341 5000000000 10742613438199 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104467349/10000000000 : ℝ)^2059 ≤ (2512795770597/20000000000000 : ℝ)^1547 := by
    have hnat : (2104467349 : ℕ)^2059*20000000000000^1547 ≤ 2512795770597^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104467349 10000000000 2512795770597 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439359701/10000000000 : ℝ)^2059 ≤ (8893113474239/20000000000000 : ℝ)^1547 := by
    have hnat : (5439359701 : ℕ)^2059*20000000000000^1547 ≤ 8893113474239^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439359701 10000000000 8893113474239 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650681341/5000000000 : ℝ), (-2104467349/10000000000 : ℝ), (5439359701/10000000000 : ℝ)] ![(10742613438199/25000000000000 : ℝ), (2512795770597/20000000000000 : ℝ), (8893113474239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650681341/5000000000 : ℝ)|^2059 ≤ (10742613438199/25000000000000 : ℝ)^1547
        have hw : |(2650681341/5000000000 : ℝ)|=(2650681341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104467349/10000000000 : ℝ)|^2059 ≤ (2512795770597/20000000000000 : ℝ)^1547
        have hw : |(-2104467349/10000000000 : ℝ)|=(2104467349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439359701/10000000000 : ℝ)|^2059 ≤ (8893113474239/20000000000000 : ℝ)^1547
        have hw : |(5439359701/10000000000 : ℝ)|=(5439359701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301362311/10000000000 : ℝ)*x 0 + (543936021/1000000000 : ℝ)*x 1 + (-1052233579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301362311/10000000000 : ℝ)^2059 ≤ (42970449750379/100000000000000 : ℝ)^1547 := by
    have hnat : (5301362311 : ℕ)^2059*100000000000000^1547 ≤ 42970449750379^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301362311 10000000000 42970449750379 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543936021/1000000000 : ℝ)^2059 ≤ (44465572909283/100000000000000 : ℝ)^1547 := by
    have hnat : (543936021 : ℕ)^2059*100000000000000^1547 ≤ 44465572909283^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543936021 1000000000 44465572909283 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052233579/5000000000 : ℝ)^2059 ≤ (1256397733529/10000000000000 : ℝ)^1547 := by
    have hnat : (1052233579 : ℕ)^2059*10000000000000^1547 ≤ 1256397733529^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052233579 5000000000 1256397733529 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301362311/10000000000 : ℝ), (543936021/1000000000 : ℝ), (-1052233579/5000000000 : ℝ)] ![(42970449750379/100000000000000 : ℝ), (44465572909283/100000000000000 : ℝ), (1256397733529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301362311/10000000000 : ℝ)|^2059 ≤ (42970449750379/100000000000000 : ℝ)^1547
        have hw : |(5301362311/10000000000 : ℝ)|=(5301362311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543936021/1000000000 : ℝ)|^2059 ≤ (44465572909283/100000000000000 : ℝ)^1547
        have hw : |(543936021/1000000000 : ℝ)|=(543936021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052233579/5000000000 : ℝ)|^2059 ≤ (1256397733529/10000000000000 : ℝ)^1547
        have hw : |(-1052233579/5000000000 : ℝ)|=(1052233579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s3_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (175034617/400000000 : ℝ)*x 0 + (2296209643/5000000000 : ℝ)*x 1 + (4169783611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175034617/400000000 : ℝ)^2059 ≤ (33286593494441/100000000000000 : ℝ)^1547 := by
    have hnat : (175034617 : ℕ)^2059*100000000000000^1547 ≤ 33286593494441^1547*400000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175034617 400000000 33286593494441 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296209643/5000000000 : ℝ)^2059 ≤ (35496843145049/100000000000000 : ℝ)^1547 := by
    have hnat : (2296209643 : ℕ)^2059*100000000000000^1547 ≤ 35496843145049^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296209643 5000000000 35496843145049 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169783611/10000000000 : ℝ)^2059 ≤ (31216563350677/100000000000000 : ℝ)^1547 := by
    have hnat : (4169783611 : ℕ)^2059*100000000000000^1547 ≤ 31216563350677^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169783611 10000000000 31216563350677 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175034617/400000000 : ℝ), (2296209643/5000000000 : ℝ), (4169783611/10000000000 : ℝ)] ![(33286593494441/100000000000000 : ℝ), (35496843145049/100000000000000 : ℝ), (31216563350677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175034617/400000000 : ℝ)|^2059 ≤ (33286593494441/100000000000000 : ℝ)^1547
        have hw : |(175034617/400000000 : ℝ)|=(175034617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296209643/5000000000 : ℝ)|^2059 ≤ (35496843145049/100000000000000 : ℝ)^1547
        have hw : |(2296209643/5000000000 : ℝ)|=(2296209643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169783611/10000000000 : ℝ)|^2059 ≤ (31216563350677/100000000000000 : ℝ)^1547
        have hw : |(4169783611/10000000000 : ℝ)|=(4169783611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5159/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (747/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8409/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4299/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8409/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4299/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8409/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4299/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8409/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4299/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8409/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4299/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8409/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4299/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4299/50000 : ℝ) ^ (8235/2048 : ℝ) ≤ (5190584576099217/100000000000000000000 : ℝ) := by
    have hpowers : (4299/50000 : ℝ)^8235 ≤ (5190584576099217/100000000000000000000 : ℝ)^2048 := by
      have hnat : (4299 : ℕ)^8235*100000000000000000000^2048 ≤ 5190584576099217^2048*50000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4299 50000 5190584576099217 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4299/50000 : ℝ)) (X := (5190584576099217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8409/50000 : ℝ) ^ (8235/2048 : ℝ) ≤ (38531124394176319/50000000000000000000 : ℝ) := by
    have hpowers : (8409/50000 : ℝ)^8235 ≤ (38531124394176319/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8409 : ℕ)^8235*50000000000000000000^2048 ≤ 38531124394176319^2048*50000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8409 50000 38531124394176319 50000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8409/50000 : ℝ)) (X := (38531124394176319/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005190584576099217/50000000000000000000 : ℝ) ≤ (2500064540999909/2500000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50005190584576099217/50000000000000000000 : ℝ)^2048 ≤ (2500064540999909/2500000000000000 : ℝ)^8235 := by
      have hnat : (50005190584576099217 : ℕ)^2048*2500000000000000^8235 ≤ 2500064540999909^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005190584576099217 50000000000000000000 2500064540999909 2500000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500064540999909/2500000000000000 : ℝ)) (X := (50005190584576099217/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20016450566672890371/20000000000000000000 : ℝ) ≤ (2500511237941749/2500000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (20016450566672890371/20000000000000000000 : ℝ)^2048 ≤ (2500511237941749/2500000000000000 : ℝ)^8235 := by
      have hnat : (20016450566672890371 : ℕ)^2048*2500000000000000^8235 ≤ 2500511237941749^8235*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20016450566672890371 20000000000000000000 2500511237941749 2500000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500511237941749/2500000000000000 : ℝ)) (X := (20016450566672890371/20000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25038531124394176319/25000000000000000000 : ℝ) ≤ (2500957934883589/2500000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (25038531124394176319/25000000000000000000 : ℝ)^2048 ≤ (2500957934883589/2500000000000000 : ℝ)^8235 := by
      have hnat : (25038531124394176319 : ℕ)^2048*2500000000000000^8235 ≤ 2500957934883589^8235*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038531124394176319 25000000000000000000 2500957934883589 2500000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500957934883589/2500000000000000 : ℝ)) (X := (25038531124394176319/25000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5190584576099217/100000000000000000000 : ℝ) ≤ ((342380818773456189/342500000000000000 : ℝ)+2*(5583711773/2568750000000 : ℝ)*(4299/50000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (342380818773456189/342500000000000000 : ℝ)+2*(5583711773/2568750000000 : ℝ)*(4299/50000 : ℝ)=(2500064540999909/2500000000000000 : ℝ) by norm_num, show 1+2*(5190584576099217/100000000000000000000 : ℝ)=(50005190584576099217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38531124394176319/50000000000000000000 : ℝ)+(5190584576099217/100000000000000000000 : ℝ) ≤ ((342380818773456189/342500000000000000 : ℝ)+(5583711773/2568750000000 : ℝ)*((8409/50000 : ℝ)+(4299/50000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (342380818773456189/342500000000000000 : ℝ)+(5583711773/2568750000000 : ℝ)*((8409/50000 : ℝ)+(4299/50000 : ℝ))=(2500511237941749/2500000000000000 : ℝ) by norm_num, show 1+(38531124394176319/50000000000000000000 : ℝ)+(5190584576099217/100000000000000000000 : ℝ)=(20016450566672890371/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38531124394176319/50000000000000000000 : ℝ) ≤ ((342380818773456189/342500000000000000 : ℝ)+2*(5583711773/2568750000000 : ℝ)*(8409/50000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (342380818773456189/342500000000000000 : ℝ)+2*(5583711773/2568750000000 : ℝ)*(8409/50000 : ℝ)=(2500957934883589/2500000000000000 : ℝ) by norm_num, show 1+2*(38531124394176319/50000000000000000000 : ℝ)=(25038531124394176319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (342380818773456189/342500000000000000 : ℝ)*(X 1 0+X 2 0)+(5583711773/2568750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (4299/50000 : ℝ)) (hi := (8409/50000 : ℝ)) (c := (342380818773456189/342500000000000000 : ℝ)) (alpha := (5583711773/2568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (342380818773456189/342500000000000000 : ℝ)*(X 0 1+X 2 1)+(5583711773/2568750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (4299/50000 : ℝ)) (hi := (8409/50000 : ℝ)) (c := (342380818773456189/342500000000000000 : ℝ)) (alpha := (5583711773/2568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (342380818773456189/342500000000000000 : ℝ)*(X 0 2+X 1 2)+(5583711773/2568750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (4299/50000 : ℝ)) (hi := (8409/50000 : ℝ)) (c := (342380818773456189/342500000000000000 : ℝ)) (alpha := (5583711773/2568750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2210076871/10000000000 : ℝ)*X 0 0+(272013799/500000000 : ℝ)*X 0 1+(5221814713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071258653/2000000000 : ℝ)*X 1 0+(-2322012523/10000000000 : ℝ)*X 1 1+(1305453639/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356293163/10000000000 : ℝ)*X 2 0+(5221814409/10000000000 : ℝ)*X 2 1+(-2322012849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273488683/625000000 : ℝ)*X 0 0+(2083997837/5000000000 : ℝ)*X 0 1+(4594196519/10000000000 : ℝ)*X 0 2+(273488683/625000000 : ℝ)*X 1 0+(2083997837/5000000000 : ℝ)*X 1 1+(4594196519/10000000000 : ℝ)*X 1 2+(273488683/625000000 : ℝ)*X 2 0+(2083997837/5000000000 : ℝ)*X 2 1+(4594196519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210100629/10000000000 : ℝ)*X 0 0+(81605077/156250000 : ℝ)*X 0 1+(5439360343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650681341/5000000000 : ℝ)*X 1 0+(-2104467349/10000000000 : ℝ)*X 1 1+(5439359701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301362311/10000000000 : ℝ)*X 2 0+(543936021/1000000000 : ℝ)*X 2 1+(-1052233579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((175034617/400000000 : ℝ)*X 0 0+(2296209643/5000000000 : ℝ)*X 0 1+(4169783611/10000000000 : ℝ)*X 0 2+(175034617/400000000 : ℝ)*X 1 0+(2296209643/5000000000 : ℝ)*X 1 1+(4169783611/10000000000 : ℝ)*X 1 2+(175034617/400000000 : ℝ)*X 2 0+(2296209643/5000000000 : ℝ)*X 2 1+(4169783611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140143510126461835970051851/17125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105644427/6250000000000 : ℝ)*(base19) + (1597136799/100000000000000 : ℝ)*(base23) + (11526873/3125000000000 : ℝ)*(upper3) + (3216113/100000000000000 : ℝ)*(upper4) + (29686941/100000000000000 : ℝ)*(upper5) + (3461927860100773/100000000000000 : ℝ)*(major0) + (3461927860100773/100000000000000 : ℝ)*(major1) + (1730963930050387/50000000000000 : ℝ)*(major2) + (28609360064203/625000000000 : ℝ)*(sp0) + (4577512786995361/100000000000000 : ℝ)*(sp1) + (915502576033879/20000000000000 : ℝ)*(sp2) + (18330658252931/781250000000 : ℝ)*(sp3) + (16867033713/100000000000000 : ℝ)*(sp4) + (3342746951/20000000000000 : ℝ)*(sp7) + (2346340970109923/100000000000000 : ℝ)*(f.failure) + (4577514477306193/100000000000000 : ℝ)*(f.sum) + (645300883927/342500000000000000000000000 : ℝ)*base66 + (1404806911820902291/102750000000000000000000000000000 : ℝ)*base67 + (830853137369785429/51375000000000000000000000000000 : ℝ)*base69 + (551135948671402291/102750000000000000000000000000000 : ℝ)*base71 + (2817348618301/685000000000000000000000000 : ℝ)*base73 + (572178321258910429/51375000000000000000000000000000 : ℝ)*base75 + (171354765517797709/102750000000000000000000000000000 : ℝ)*base78 + (511598945661452291/102750000000000000000000000000000 : ℝ)*base79 + (3600975298327/1027500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (11597601/10000000000000000000000 : ℝ)*base90 + (11597601/10000000000000000000000 : ℝ)*base92 + (111597601/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (791119407937575346563/137000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1144363097/100000000000000 : ℝ)*(base19) + (164104759/20000000000000 : ℝ)*(base23) + (13285349/100000000000000 : ℝ)*(lower4) + (258134529/100000000000000 : ℝ)*(upper5) + (69821622024663/2000000000000 : ℝ)*(major0) + (69821622024663/2000000000000 : ℝ)*(major1) + (69821622024663/2000000000000 : ℝ)*(major2) + (3215925947/100000000000000 : ℝ)*(sp0) + (13583971811/100000000000000 : ℝ)*(sp1) + (11088326333/100000000000000 : ℝ)*(sp2) + (4616059051709339/100000000000000 : ℝ)*(sp4) + (2308023769650189/50000000000000 : ℝ)*(sp5) + (2308025179392579/50000000000000 : ℝ)*(sp6) + (473219948468907/20000000000000 : ℝ)*(sp7) + (473219948468907/20000000000000 : ℝ)*(f.failure) + (2308031133817643/50000000000000 : ℝ)*(f.sum) + (585550819221/137000000000000000000000000 : ℝ)*base65 + (1987768857280693/685000000000000000000000000000 : ℝ)*base68 + (944332740684307/685000000000000000000000000000 : ℝ)*base69 + (3114254017279307/685000000000000000000000000000 : ℝ)*base71 + (24923178563/27400000000000000000000000 : ℝ)*base74 + (1000265452574307/685000000000000000000000000000 : ℝ)*base75 + (585632856330693/685000000000000000000000000000 : ℝ)*base78 + (2665055568905693/685000000000000000000000000000 : ℝ)*base80 + (55390047833/34250000000000000000000000 : ℝ)*base81 + (11463609/2000000000000000000000 : ℝ)*base90 + (11463609/2000000000000000000000 : ℝ)*base92 + (11463609/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (747/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_s4_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213990259/10000000000 : ℝ)*x 0 + (2703560461/5000000000 : ℝ)*x 1 + (2626206967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213990259/10000000000 : ℝ)^2059 ≤ (13441662654211/100000000000000 : ℝ)^1547 := by
    have hnat : (2213990259 : ℕ)^2059*100000000000000^1547 ≤ 13441662654211^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213990259 10000000000 13441662654211 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703560461/5000000000 : ℝ)^2059 ≤ (22057571643563/50000000000000 : ℝ)^1547 := by
    have hnat : (2703560461 : ℕ)^2059*50000000000000^1547 ≤ 22057571643563^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703560461 5000000000 22057571643563 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626206967/5000000000 : ℝ)^2059 ≤ (42443194037513/100000000000000 : ℝ)^1547 := by
    have hnat : (2626206967 : ℕ)^2059*100000000000000^1547 ≤ 42443194037513^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626206967 5000000000 42443194037513 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213990259/10000000000 : ℝ), (2703560461/5000000000 : ℝ), (2626206967/5000000000 : ℝ)] ![(13441662654211/100000000000000 : ℝ), (22057571643563/50000000000000 : ℝ), (42443194037513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213990259/10000000000 : ℝ)|^2059 ≤ (13441662654211/100000000000000 : ℝ)^1547
        have hw : |(-2213990259/10000000000 : ℝ)|=(2213990259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703560461/5000000000 : ℝ)|^2059 ≤ (22057571643563/50000000000000 : ℝ)^1547
        have hw : |(2703560461/5000000000 : ℝ)|=(2703560461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626206967/5000000000 : ℝ)|^2059 ≤ (42443194037513/100000000000000 : ℝ)^1547
        have hw : |(2626206967/5000000000 : ℝ)|=(2626206967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348100089/10000000000 : ℝ)*x 0 + (-2292701131/10000000000 : ℝ)*x 1 + (5252413957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348100089/10000000000 : ℝ)^2059 ≤ (43475399783839/100000000000000 : ℝ)^1547 := by
    have hnat : (5348100089 : ℕ)^2059*100000000000000^1547 ≤ 43475399783839^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348100089 10000000000 43475399783839 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2292701131/10000000000 : ℝ)^2059 ≤ (7040702959551/50000000000000 : ℝ)^1547 := by
    have hnat : (2292701131 : ℕ)^2059*50000000000000^1547 ≤ 7040702959551^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292701131 10000000000 7040702959551 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252413957/10000000000 : ℝ)^2059 ≤ (42443194284881/100000000000000 : ℝ)^1547 := by
    have hnat : (5252413957 : ℕ)^2059*100000000000000^1547 ≤ 42443194284881^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252413957 10000000000 42443194284881 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348100089/10000000000 : ℝ), (-2292701131/10000000000 : ℝ), (5252413957/10000000000 : ℝ)] ![(43475399783839/100000000000000 : ℝ), (7040702959551/50000000000000 : ℝ), (42443194284881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348100089/10000000000 : ℝ)|^2059 ≤ (43475399783839/100000000000000 : ℝ)^1547
        have hw : |(5348100089/10000000000 : ℝ)|=(5348100089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2292701131/10000000000 : ℝ)|^2059 ≤ (7040702959551/50000000000000 : ℝ)^1547
        have hw : |(-2292701131/10000000000 : ℝ)|=(2292701131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252413957/10000000000 : ℝ)|^2059 ≤ (42443194284881/100000000000000 : ℝ)^1547
        have hw : |(5252413957/10000000000 : ℝ)|=(5252413957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674050067/5000000000 : ℝ)*x 0 + (1050482777/2000000000 : ℝ)*x 1 + (-458540233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674050067/5000000000 : ℝ)^2059 ≤ (43475400270719/100000000000000 : ℝ)^1547 := by
    have hnat : (2674050067 : ℕ)^2059*100000000000000^1547 ≤ 43475400270719^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674050067 5000000000 43475400270719 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050482777/2000000000 : ℝ)^2059 ≤ (2652699594407/6250000000000 : ℝ)^1547 := by
    have hnat : (1050482777 : ℕ)^2059*6250000000000^1547 ≤ 2652699594407^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050482777 2000000000 2652699594407 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458540233/2000000000 : ℝ)^2059 ≤ (14081406197037/100000000000000 : ℝ)^1547 := by
    have hnat : (458540233 : ℕ)^2059*100000000000000^1547 ≤ 14081406197037^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458540233 2000000000 14081406197037 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674050067/5000000000 : ℝ), (1050482777/2000000000 : ℝ), (-458540233/2000000000 : ℝ)] ![(43475400270719/100000000000000 : ℝ), (2652699594407/6250000000000 : ℝ), (14081406197037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674050067/5000000000 : ℝ)|^2059 ≤ (43475400270719/100000000000000 : ℝ)^1547
        have hw : |(2674050067/5000000000 : ℝ)|=(2674050067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050482777/2000000000 : ℝ)|^2059 ≤ (2652699594407/6250000000000 : ℝ)^1547
        have hw : |(1050482777/2000000000 : ℝ)|=(1050482777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458540233/2000000000 : ℝ)|^2059 ≤ (14081406197037/100000000000000 : ℝ)^1547
        have hw : |(-458540233/2000000000 : ℝ)|=(458540233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2189071027/5000000000 : ℝ)*x 0 + (2114939999/5000000000 : ℝ)*x 1 + (70807819/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189071027/5000000000 : ℝ)^2059 ≤ (33309645094511/100000000000000 : ℝ)^1547 := by
    have hnat : (2189071027 : ℕ)^2059*100000000000000^1547 ≤ 33309645094511^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189071027 5000000000 33309645094511 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114939999/5000000000 : ℝ)^2059 ≤ (795419817109/2500000000000 : ℝ)^1547 := by
    have hnat : (2114939999 : ℕ)^2059*2500000000000^1547 ≤ 795419817109^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114939999 5000000000 795419817109 2500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70807819/156250000 : ℝ)^2059 ≤ (8718390551371/25000000000000 : ℝ)^1547 := by
    have hnat : (70807819 : ℕ)^2059*25000000000000^1547 ≤ 8718390551371^1547*156250000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70807819 156250000 8718390551371 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189071027/5000000000 : ℝ), (2114939999/5000000000 : ℝ), (70807819/156250000 : ℝ)] ![(33309645094511/100000000000000 : ℝ), (795419817109/2500000000000 : ℝ), (8718390551371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189071027/5000000000 : ℝ)|^2059 ≤ (33309645094511/100000000000000 : ℝ)^1547
        have hw : |(2189071027/5000000000 : ℝ)|=(2189071027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114939999/5000000000 : ℝ)|^2059 ≤ (795419817109/2500000000000 : ℝ)^1547
        have hw : |(2114939999/5000000000 : ℝ)|=(2114939999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70807819/156250000 : ℝ)|^2059 ≤ (8718390551371/25000000000000 : ℝ)^1547
        have hw : |(70807819/156250000 : ℝ)|=(70807819/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213998943/10000000000 : ℝ)*x 0 + (1313217857/2500000000 : ℝ)*x 1 + (5406661327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213998943/10000000000 : ℝ)^2059 ≤ (672086641307/5000000000000 : ℝ)^1547 := by
    have hnat : (2213998943 : ℕ)^2059*5000000000000^1547 ≤ 672086641307^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213998943 10000000000 672086641307 5000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313217857/2500000000 : ℝ)^2059 ≤ (42448114510019/100000000000000 : ℝ)^1547 := by
    have hnat : (1313217857 : ℕ)^2059*100000000000000^1547 ≤ 42448114510019^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313217857 2500000000 42448114510019 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406661327/10000000000 : ℝ)^2059 ≤ (11027538160091/25000000000000 : ℝ)^1547 := by
    have hnat : (5406661327 : ℕ)^2059*25000000000000^1547 ≤ 11027538160091^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406661327 10000000000 11027538160091 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213998943/10000000000 : ℝ), (1313217857/2500000000 : ℝ), (5406661327/10000000000 : ℝ)] ![(672086641307/5000000000000 : ℝ), (42448114510019/100000000000000 : ℝ), (11027538160091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213998943/10000000000 : ℝ)|^2059 ≤ (672086641307/5000000000000 : ℝ)^1547
        have hw : |(-2213998943/10000000000 : ℝ)|=(2213998943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313217857/2500000000 : ℝ)|^2059 ≤ (42448114510019/100000000000000 : ℝ)^1547
        have hw : |(1313217857/2500000000 : ℝ)|=(1313217857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406661327/10000000000 : ℝ)|^2059 ≤ (11027538160091/25000000000000 : ℝ)^1547
        have hw : |(5406661327/10000000000 : ℝ)|=(5406661327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2654603109/5000000000 : ℝ)*x 0 + (-2138453811/10000000000 : ℝ)*x 1 + (5406661271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654603109/5000000000 : ℝ)^2059 ≤ (21527545997261/50000000000000 : ℝ)^1547 := by
    have hnat : (2654603109 : ℕ)^2059*50000000000000^1547 ≤ 21527545997261^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654603109 5000000000 21527545997261 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2138453811/10000000000 : ℝ)^2059 ≤ (6417377980533/50000000000000 : ℝ)^1547 := by
    have hnat : (2138453811 : ℕ)^2059*50000000000000^1547 ≤ 6417377980533^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138453811 10000000000 6417377980533 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406661271/10000000000 : ℝ)^2059 ≤ (1102753800807/2500000000000 : ℝ)^1547 := by
    have hnat : (5406661271 : ℕ)^2059*2500000000000^1547 ≤ 1102753800807^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406661271 10000000000 1102753800807 2500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654603109/5000000000 : ℝ), (-2138453811/10000000000 : ℝ), (5406661271/10000000000 : ℝ)] ![(21527545997261/50000000000000 : ℝ), (6417377980533/50000000000000 : ℝ), (1102753800807/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654603109/5000000000 : ℝ)|^2059 ≤ (21527545997261/50000000000000 : ℝ)^1547
        have hw : |(2654603109/5000000000 : ℝ)|=(2654603109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2138453811/10000000000 : ℝ)|^2059 ≤ (6417377980533/50000000000000 : ℝ)^1547
        have hw : |(-2138453811/10000000000 : ℝ)|=(2138453811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406661271/10000000000 : ℝ)|^2059 ≤ (1102753800807/2500000000000 : ℝ)^1547
        have hw : |(5406661271/10000000000 : ℝ)|=(5406661271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5309206169/10000000000 : ℝ)*x 0 + (2703330649/5000000000 : ℝ)*x 1 + (-26730673/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309206169/10000000000 : ℝ)^2059 ≤ (21527545732821/50000000000000 : ℝ)^1547 := by
    have hnat : (5309206169 : ℕ)^2059*50000000000000^1547 ≤ 21527545732821^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309206169 10000000000 21527545732821 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703330649/5000000000 : ℝ)^2059 ≤ (44110152325463/100000000000000 : ℝ)^1547 := by
    have hnat : (2703330649 : ℕ)^2059*100000000000000^1547 ≤ 44110152325463^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703330649 5000000000 44110152325463 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26730673/125000000 : ℝ)^2059 ≤ (12834756192727/100000000000000 : ℝ)^1547 := by
    have hnat : (26730673 : ℕ)^2059*100000000000000^1547 ≤ 12834756192727^1547*125000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26730673 125000000 12834756192727 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309206169/10000000000 : ℝ), (2703330649/5000000000 : ℝ), (-26730673/125000000 : ℝ)] ![(21527545732821/50000000000000 : ℝ), (44110152325463/100000000000000 : ℝ), (12834756192727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309206169/10000000000 : ℝ)|^2059 ≤ (21527545732821/50000000000000 : ℝ)^1547
        have hw : |(5309206169/10000000000 : ℝ)|=(5309206169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703330649/5000000000 : ℝ)|^2059 ≤ (44110152325463/100000000000000 : ℝ)^1547
        have hw : |(2703330649/5000000000 : ℝ)|=(2703330649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26730673/125000000 : ℝ)|^2059 ≤ (12834756192727/100000000000000 : ℝ)^1547
        have hw : |(-26730673/125000000 : ℝ)|=(26730673/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s4_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (218907929/500000000 : ℝ)*x 0 + (4530807161/10000000000 : ℝ)*x 1 + (4230777087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218907929/500000000 : ℝ)^2059 ≤ (8327453110019/25000000000000 : ℝ)^1547 := by
    have hnat : (218907929 : ℕ)^2059*25000000000000^1547 ≤ 8327453110019^1547*500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218907929 500000000 8327453110019 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530807161/10000000000 : ℝ)^2059 ≤ (34864413441131/100000000000000 : ℝ)^1547 := by
    have hnat : (4530807161 : ℕ)^2059*100000000000000^1547 ≤ 34864413441131^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530807161 10000000000 34864413441131 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230777087/10000000000 : ℝ)^2059 ≤ (7956443526871/25000000000000 : ℝ)^1547 := by
    have hnat : (4230777087 : ℕ)^2059*25000000000000^1547 ≤ 7956443526871^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230777087 10000000000 7956443526871 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218907929/500000000 : ℝ), (4530807161/10000000000 : ℝ), (4230777087/10000000000 : ℝ)] ![(8327453110019/25000000000000 : ℝ), (34864413441131/100000000000000 : ℝ), (7956443526871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218907929/500000000 : ℝ)|^2059 ≤ (8327453110019/25000000000000 : ℝ)^1547
        have hw : |(218907929/500000000 : ℝ)|=(218907929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530807161/10000000000 : ℝ)|^2059 ≤ (34864413441131/100000000000000 : ℝ)^1547
        have hw : |(4530807161/10000000000 : ℝ)|=(4530807161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230777087/10000000000 : ℝ)|^2059 ≤ (7956443526871/25000000000000 : ℝ)^1547
        have hw : |(4230777087/10000000000 : ℝ)|=(4230777087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (747/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2743/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (747/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5159/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (747/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5159/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (747/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5159/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (747/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5159/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (747/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5159/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (747/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5159/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5159/50000 : ℝ) ^ (8235/2048 : ℝ) ≤ (10806161485722589/100000000000000000000 : ℝ) := by
    have hpowers : (5159/50000 : ℝ)^8235 ≤ (10806161485722589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5159 : ℕ)^8235*100000000000000000000^2048 ≤ 10806161485722589^2048*50000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5159 50000 10806161485722589 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5159/50000 : ℝ)) (X := (10806161485722589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (747/5000 : ℝ) ^ (8235/2048 : ℝ) ≤ (47870391318813587/100000000000000000000 : ℝ) := by
    have hpowers : (747/5000 : ℝ)^8235 ≤ (47870391318813587/100000000000000000000 : ℝ)^2048 := by
      have hnat : (747 : ℕ)^8235*100000000000000000000^2048 ≤ 47870391318813587^2048*5000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        747 5000 47870391318813587 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (747/5000 : ℝ)) (X := (47870391318813587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010806161485722589/50000000000000000000 : ℝ) ≤ (10000537443161927/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50010806161485722589/50000000000000000000 : ℝ)^2048 ≤ (10000537443161927/10000000000000000 : ℝ)^8235 := by
      have hnat : (50010806161485722589 : ℕ)^2048*10000000000000000^8235 ≤ 10000537443161927^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010806161485722589 50000000000000000000 10000537443161927 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537443161927/10000000000000000 : ℝ)) (X := (50010806161485722589/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253667284550283511/6250000000000000000 : ℝ) ≤ (1000145893262207/1000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (6253667284550283511/6250000000000000000 : ℝ)^2048 ≤ (1000145893262207/1000000000000000 : ℝ)^8235 := by
      have hnat : (6253667284550283511 : ℕ)^2048*1000000000000000^8235 ≤ 1000145893262207^8235*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253667284550283511 6250000000000000000 1000145893262207 1000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000145893262207/1000000000000000 : ℝ)) (X := (6253667284550283511/6250000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047870391318813587/50000000000000000000 : ℝ) ≤ (10002380422082213/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50047870391318813587/50000000000000000000 : ℝ)^2048 ≤ (10002380422082213/10000000000000000 : ℝ)^8235 := by
      have hnat : (50047870391318813587 : ℕ)^2048*10000000000000000^8235 ≤ 10002380422082213^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047870391318813587 50000000000000000000 10002380422082213 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002380422082213/10000000000000000 : ℝ)) (X := (50047870391318813587/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10806161485722589/100000000000000000000 : ℝ) ≤ ((23101734102897457823/23110000000000000000 : ℝ)+2*(921489460143/462200000000000 : ℝ)*(5159/50000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (23101734102897457823/23110000000000000000 : ℝ)+2*(921489460143/462200000000000 : ℝ)*(5159/50000 : ℝ)=(10000537443161927/10000000000000000 : ℝ) by norm_num, show 1+2*(10806161485722589/100000000000000000000 : ℝ)=(50010806161485722589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47870391318813587/100000000000000000000 : ℝ)+(10806161485722589/100000000000000000000 : ℝ) ≤ ((23101734102897457823/23110000000000000000 : ℝ)+(921489460143/462200000000000 : ℝ)*((747/5000 : ℝ)+(5159/50000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (23101734102897457823/23110000000000000000 : ℝ)+(921489460143/462200000000000 : ℝ)*((747/5000 : ℝ)+(5159/50000 : ℝ))=(1000145893262207/1000000000000000 : ℝ) by norm_num, show 1+(47870391318813587/100000000000000000000 : ℝ)+(10806161485722589/100000000000000000000 : ℝ)=(6253667284550283511/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47870391318813587/100000000000000000000 : ℝ) ≤ ((23101734102897457823/23110000000000000000 : ℝ)+2*(921489460143/462200000000000 : ℝ)*(747/5000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (23101734102897457823/23110000000000000000 : ℝ)+2*(921489460143/462200000000000 : ℝ)*(747/5000 : ℝ)=(10002380422082213/10000000000000000 : ℝ) by norm_num, show 1+2*(47870391318813587/100000000000000000000 : ℝ)=(50047870391318813587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23101734102897457823/23110000000000000000 : ℝ)*(X 1 0+X 2 0)+(921489460143/462200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (5159/50000 : ℝ)) (hi := (747/5000 : ℝ)) (c := (23101734102897457823/23110000000000000000 : ℝ)) (alpha := (921489460143/462200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23101734102897457823/23110000000000000000 : ℝ)*(X 0 1+X 2 1)+(921489460143/462200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (5159/50000 : ℝ)) (hi := (747/5000 : ℝ)) (c := (23101734102897457823/23110000000000000000 : ℝ)) (alpha := (921489460143/462200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23101734102897457823/23110000000000000000 : ℝ)*(X 0 2+X 1 2)+(921489460143/462200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (5159/50000 : ℝ)) (hi := (747/5000 : ℝ)) (c := (23101734102897457823/23110000000000000000 : ℝ)) (alpha := (921489460143/462200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2213990259/10000000000 : ℝ)*X 0 0+(2703560461/5000000000 : ℝ)*X 0 1+(2626206967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348100089/10000000000 : ℝ)*X 1 0+(-2292701131/10000000000 : ℝ)*X 1 1+(5252413957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674050067/5000000000 : ℝ)*X 2 0+(1050482777/2000000000 : ℝ)*X 2 1+(-458540233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189071027/5000000000 : ℝ)*X 0 0+(2114939999/5000000000 : ℝ)*X 0 1+(70807819/156250000 : ℝ)*X 0 2+(2189071027/5000000000 : ℝ)*X 1 0+(2114939999/5000000000 : ℝ)*X 1 1+(70807819/156250000 : ℝ)*X 1 2+(2189071027/5000000000 : ℝ)*X 2 0+(2114939999/5000000000 : ℝ)*X 2 1+(70807819/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2213998943/10000000000 : ℝ)*X 0 0+(1313217857/2500000000 : ℝ)*X 0 1+(5406661327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654603109/5000000000 : ℝ)*X 1 0+(-2138453811/10000000000 : ℝ)*X 1 1+(5406661271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309206169/10000000000 : ℝ)*X 2 0+(2703330649/5000000000 : ℝ)*X 2 1+(-26730673/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218907929/500000000 : ℝ)*X 0 0+(4530807161/10000000000 : ℝ)*X 0 1+(4230777087/10000000000 : ℝ)*X 0 2+(218907929/500000000 : ℝ)*X 1 0+(4530807161/10000000000 : ℝ)*X 1 1+(4230777087/10000000000 : ℝ)*X 1 2+(218907929/500000000 : ℝ)*X 2 0+(4530807161/10000000000 : ℝ)*X 2 1+(4230777087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10152241147916776943487/2311000000000000000000000000 : ℝ) := by norm_num
    linear_combination (960476613/100000000000000 : ℝ)*(base19) + (981205891/100000000000000 : ℝ)*(base23) + (281269/1562500000000 : ℝ)*(lower2) + (138377693/100000000000000 : ℝ)*(upper3) + (617337/800000000000 : ℝ)*(upper5) + (488856433145837/10000000000000 : ℝ)*(major0) + (488856433145837/10000000000000 : ℝ)*(major1) + (488856433145837/10000000000000 : ℝ)*(major2) + (3231927571677827/50000000000000 : ℝ)*(sp0) + (3231937869053079/50000000000000 : ℝ)*(sp1) + (6463875717376881/100000000000000 : ℝ)*(sp2) + (51769365241847/1562500000000 : ℝ)*(sp3) + (10777613559/50000000000000 : ℝ)*(sp4) + (6221211077/50000000000000 : ℝ)*(sp7) + (1656625908950181/50000000000000 : ℝ)*(f.failure) + (6463876698582771/100000000000000 : ℝ)*(f.sum) + (24018561794279/2311000000000000000000000000 : ℝ)*base65 + (1276262769093082851/231100000000000000000000000000000 : ℝ)*base67 + (102008959572717149/231100000000000000000000000000000 : ℝ)*base70 + (390853326954682851/231100000000000000000000000000000 : ℝ)*base71 + (9654172889789/2311000000000000000000000000 : ℝ)*base74 + (760019708555117149/231100000000000000000000000000000 : ℝ)*base76 + (595757219403482851/231100000000000000000000000000000 : ℝ)*base77 + (415161642009217149/231100000000000000000000000000000 : ℝ)*base80 + (150910949761/115550000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (67857847/5000000000000000000000 : ℝ)*base90 + (67857847/5000000000000000000000 : ℝ)*base92 + (67857847/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5801996179323280303149460377/577750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286494503/12500000000000 : ℝ)*(base19) + (2312947757/100000000000000 : ℝ)*(base23) + (39482677/50000000000000 : ℝ)*(upper2) + (58763253/50000000000000 : ℝ)*(upper3) + (113513509/25000000000000 : ℝ)*(upper5) + (2458845270318867/50000000000000 : ℝ)*(major0) + (2458845270318867/50000000000000 : ℝ)*(major1) + (2458845270318867/50000000000000 : ℝ)*(major2) + (29136103993/50000000000000 : ℝ)*(sp1) + (12256686593/25000000000000 : ℝ)*(sp2) + (6502388477451193/100000000000000 : ℝ)*(sp4) + (6502327913287183/100000000000000 : ℝ)*(sp5) + (812792142219633/12500000000000 : ℝ)*(sp6) + (833248067269407/25000000000000 : ℝ)*(sp7) + (833248067269407/25000000000000 : ℝ)*(f.failure) + (6502388477451193/100000000000000 : ℝ)*(f.sum) + (26237583694113/5777500000000000000000000000 : ℝ)*base65 + (4321049360576696541/1155500000000000000000000000000000 : ℝ)*base67 + (664683337634196541/1155500000000000000000000000000000 : ℝ)*base69 + (4609989445291303459/1155500000000000000000000000000000 : ℝ)*base72 + (18519431335193/5777500000000000000000000000 : ℝ)*base73 + (9010932537072196541/1155500000000000000000000000000000 : ℝ)*base75 + (320613387720696541/1155500000000000000000000000000000 : ℝ)*base77 + (6248159719407303459/1155500000000000000000000000000000 : ℝ)*base80 + (94689034386701/11555000000000000000000000000 : ℝ)*base81 + (4157109/2500000000000000000000 : ℝ)*base90 + (4157109/2500000000000000000000 : ℝ)*base92 + (4157109/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (747/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5159/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_s5_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214884767/10000000000 : ℝ)*x 0 + (42169327/78125000 : ℝ)*x 1 + (2630637429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214884767/10000000000 : ℝ)^2059 ≤ (6724445646973/50000000000000 : ℝ)^1547 := by
    have hnat : (2214884767 : ℕ)^2059*50000000000000^1547 ≤ 6724445646973^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214884767 10000000000 6724445646973 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42169327/78125000 : ℝ)^2059 ≤ (4401258778543/10000000000000 : ℝ)^1547 := by
    have hnat : (42169327 : ℕ)^2059*10000000000000^1547 ≤ 4401258778543^1547*78125000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42169327 78125000 4401258778543 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630637429/5000000000 : ℝ)^2059 ≤ (21269260454317/50000000000000 : ℝ)^1547 := by
    have hnat : (2630637429 : ℕ)^2059*50000000000000^1547 ≤ 21269260454317^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630637429 5000000000 21269260454317 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214884767/10000000000 : ℝ), (42169327/78125000 : ℝ), (2630637429/5000000000 : ℝ)] ![(6724445646973/50000000000000 : ℝ), (4401258778543/10000000000000 : ℝ), (21269260454317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214884767/10000000000 : ℝ)|^2059 ≤ (6724445646973/50000000000000 : ℝ)^1547
        have hw : |(-2214884767/10000000000 : ℝ)|=(2214884767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42169327/78125000 : ℝ)|^2059 ≤ (4401258778543/10000000000000 : ℝ)^1547
        have hw : |(42169327/78125000 : ℝ)|=(42169327/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630637429/5000000000 : ℝ)|^2059 ≤ (21269260454317/50000000000000 : ℝ)^1547
        have hw : |(2630637429/5000000000 : ℝ)|=(2630637429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345753867/10000000000 : ℝ)*x 0 + (-456827933/2000000000 : ℝ)*x 1 + (5261274823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345753867/10000000000 : ℝ)^2059 ≤ (21725008254247/50000000000000 : ℝ)^1547 := by
    have hnat : (5345753867 : ℕ)^2059*50000000000000^1547 ≤ 21725008254247^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345753867 10000000000 21725008254247 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456827933/2000000000 : ℝ)^2059 ≤ (14011462949959/100000000000000 : ℝ)^1547 := by
    have hnat : (456827933 : ℕ)^2059*100000000000000^1547 ≤ 14011462949959^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456827933 2000000000 14011462949959 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261274823/10000000000 : ℝ)^2059 ≤ (8507704106399/20000000000000 : ℝ)^1547 := by
    have hnat : (5261274823 : ℕ)^2059*20000000000000^1547 ≤ 8507704106399^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261274823 10000000000 8507704106399 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345753867/10000000000 : ℝ), (-456827933/2000000000 : ℝ), (5261274823/10000000000 : ℝ)] ![(21725008254247/50000000000000 : ℝ), (14011462949959/100000000000000 : ℝ), (8507704106399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345753867/10000000000 : ℝ)|^2059 ≤ (21725008254247/50000000000000 : ℝ)^1547
        have hw : |(5345753867/10000000000 : ℝ)|=(5345753867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456827933/2000000000 : ℝ)|^2059 ≤ (14011462949959/100000000000000 : ℝ)^1547
        have hw : |(-456827933/2000000000 : ℝ)|=(456827933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261274823/10000000000 : ℝ)|^2059 ≤ (8507704106399/20000000000000 : ℝ)^1547
        have hw : |(5261274823/10000000000 : ℝ)|=(5261274823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672876941/5000000000 : ℝ)*x 0 + (526127483/1000000000 : ℝ)*x 1 + (-571034909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672876941/5000000000 : ℝ)^2059 ≤ (10862504167691/25000000000000 : ℝ)^1547 := by
    have hnat : (2672876941 : ℕ)^2059*25000000000000^1547 ≤ 10862504167691^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672876941 5000000000 10862504167691 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526127483/1000000000 : ℝ)^2059 ≤ (42538520607323/100000000000000 : ℝ)^1547 := by
    have hnat : (526127483 : ℕ)^2059*100000000000000^1547 ≤ 42538520607323^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526127483 1000000000 42538520607323 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571034909/2500000000 : ℝ)^2059 ≤ (1401146271319/10000000000000 : ℝ)^1547 := by
    have hnat : (571034909 : ℕ)^2059*10000000000000^1547 ≤ 1401146271319^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571034909 2500000000 1401146271319 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672876941/5000000000 : ℝ), (526127483/1000000000 : ℝ), (-571034909/2500000000 : ℝ)] ![(10862504167691/25000000000000 : ℝ), (42538520607323/100000000000000 : ℝ), (1401146271319/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672876941/5000000000 : ℝ)|^2059 ≤ (10862504167691/25000000000000 : ℝ)^1547
        have hw : |(2672876941/5000000000 : ℝ)|=(2672876941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526127483/1000000000 : ℝ)|^2059 ≤ (42538520607323/100000000000000 : ℝ)^1547
        have hw : |(526127483/1000000000 : ℝ)|=(526127483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571034909/2500000000 : ℝ)|^2059 ≤ (1401146271319/10000000000000 : ℝ)^1547
        have hw : |(-571034909/2500000000 : ℝ)|=(571034909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378662577/10000000000 : ℝ)*x 0 + (4247670091/10000000000 : ℝ)*x 1 + (4513773077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378662577/10000000000 : ℝ)^2059 ≤ (8328729028609/25000000000000 : ℝ)^1547 := by
    have hnat : (4378662577 : ℕ)^2059*25000000000000^1547 ≤ 8328729028609^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378662577 10000000000 8328729028609 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247670091/10000000000 : ℝ)^2059 ≤ (6399004017343/20000000000000 : ℝ)^1547 := by
    have hnat : (4247670091 : ℕ)^2059*20000000000000^1547 ≤ 6399004017343^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247670091 10000000000 6399004017343 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513773077/10000000000 : ℝ)^2059 ≤ (271016123317/781250000000 : ℝ)^1547 := by
    have hnat : (4513773077 : ℕ)^2059*781250000000^1547 ≤ 271016123317^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513773077 10000000000 271016123317 781250000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378662577/10000000000 : ℝ), (4247670091/10000000000 : ℝ), (4513773077/10000000000 : ℝ)] ![(8328729028609/25000000000000 : ℝ), (6399004017343/20000000000000 : ℝ), (271016123317/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378662577/10000000000 : ℝ)|^2059 ≤ (8328729028609/25000000000000 : ℝ)^1547
        have hw : |(4378662577/10000000000 : ℝ)|=(4378662577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247670091/10000000000 : ℝ)|^2059 ≤ (6399004017343/20000000000000 : ℝ)^1547
        have hw : |(4247670091/10000000000 : ℝ)|=(4247670091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513773077/10000000000 : ℝ)|^2059 ≤ (271016123317/781250000000 : ℝ)^1547
        have hw : |(4513773077/10000000000 : ℝ)|=(4513773077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-221489059/1000000000 : ℝ)*x 0 + (5261630943/10000000000 : ℝ)*x 1 + (539731643/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221489059/1000000000 : ℝ)^2059 ≤ (336223458839/2500000000000 : ℝ)^1547 := by
    have hnat : (221489059 : ℕ)^2059*2500000000000^1547 ≤ 336223458839^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221489059 1000000000 336223458839 2500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261630943/10000000000 : ℝ)^2059 ≤ (42542352824551/100000000000000 : ℝ)^1547 := by
    have hnat : (5261630943 : ℕ)^2059*100000000000000^1547 ≤ 42542352824551^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261630943 10000000000 42542352824551 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539731643/1000000000 : ℝ)^2059 ≤ (11002177201047/25000000000000 : ℝ)^1547 := by
    have hnat : (539731643 : ℕ)^2059*25000000000000^1547 ≤ 11002177201047^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539731643 1000000000 11002177201047 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221489059/1000000000 : ℝ), (5261630943/10000000000 : ℝ), (539731643/1000000000 : ℝ)] ![(336223458839/2500000000000 : ℝ), (42542352824551/100000000000000 : ℝ), (11002177201047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221489059/1000000000 : ℝ)|^2059 ≤ (336223458839/2500000000000 : ℝ)^1547
        have hw : |(-221489059/1000000000 : ℝ)|=(221489059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261630943/10000000000 : ℝ)|^2059 ≤ (42542352824551/100000000000000 : ℝ)^1547
        have hw : |(5261630943/10000000000 : ℝ)|=(5261630943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539731643/1000000000 : ℝ)|^2059 ≤ (11002177201047/25000000000000 : ℝ)^1547
        have hw : |(539731643/1000000000 : ℝ)|=(539731643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062292309/2000000000 : ℝ)*x 0 + (-2148098083/10000000000 : ℝ)*x 1 + (2698658217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062292309/2000000000 : ℝ)^2059 ≤ (43079436502659/100000000000000 : ℝ)^1547 := by
    have hnat : (1062292309 : ℕ)^2059*100000000000000^1547 ≤ 43079436502659^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062292309 2000000000 43079436502659 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148098083/10000000000 : ℝ)^2059 ≤ (12911854632933/100000000000000 : ℝ)^1547 := by
    have hnat : (2148098083 : ℕ)^2059*100000000000000^1547 ≤ 12911854632933^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148098083 10000000000 12911854632933 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698658217/5000000000 : ℝ)^2059 ≤ (22004354423799/50000000000000 : ℝ)^1547 := by
    have hnat : (2698658217 : ℕ)^2059*50000000000000^1547 ≤ 22004354423799^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698658217 5000000000 22004354423799 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062292309/2000000000 : ℝ), (-2148098083/10000000000 : ℝ), (2698658217/5000000000 : ℝ)] ![(43079436502659/100000000000000 : ℝ), (12911854632933/100000000000000 : ℝ), (22004354423799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062292309/2000000000 : ℝ)|^2059 ≤ (43079436502659/100000000000000 : ℝ)^1547
        have hw : |(1062292309/2000000000 : ℝ)|=(1062292309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148098083/10000000000 : ℝ)|^2059 ≤ (12911854632933/100000000000000 : ℝ)^1547
        have hw : |(-2148098083/10000000000 : ℝ)|=(2148098083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698658217/5000000000 : ℝ)|^2059 ≤ (22004354423799/50000000000000 : ℝ)^1547
        have hw : |(2698658217/5000000000 : ℝ)|=(2698658217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311461549/10000000000 : ℝ)*x 0 + (5397316439/10000000000 : ℝ)*x 1 + (-2148098071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311461549/10000000000 : ℝ)^2059 ≤ (43079436545839/100000000000000 : ℝ)^1547 := by
    have hnat : (5311461549 : ℕ)^2059*100000000000000^1547 ≤ 43079436545839^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311461549 10000000000 43079436545839 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397316439/10000000000 : ℝ)^2059 ≤ (2200435445093/5000000000000 : ℝ)^1547 := by
    have hnat : (5397316439 : ℕ)^2059*5000000000000^1547 ≤ 2200435445093^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397316439 10000000000 2200435445093 5000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148098071/10000000000 : ℝ)^2059 ≤ (12911854536931/100000000000000 : ℝ)^1547 := by
    have hnat : (2148098071 : ℕ)^2059*100000000000000^1547 ≤ 12911854536931^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148098071 10000000000 12911854536931 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311461549/10000000000 : ℝ), (5397316439/10000000000 : ℝ), (-2148098071/10000000000 : ℝ)] ![(43079436545839/100000000000000 : ℝ), (2200435445093/5000000000000 : ℝ), (12911854536931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311461549/10000000000 : ℝ)|^2059 ≤ (43079436545839/100000000000000 : ℝ)^1547
        have hw : |(5311461549/10000000000 : ℝ)|=(5311461549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397316439/10000000000 : ℝ)|^2059 ≤ (2200435445093/5000000000000 : ℝ)^1547
        have hw : |(5397316439/10000000000 : ℝ)|=(5397316439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148098071/10000000000 : ℝ)|^2059 ≤ (12911854536931/100000000000000 : ℝ)^1547
        have hw : |(-2148098071/10000000000 : ℝ)|=(2148098071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s5_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378673959/10000000000 : ℝ)*x 0 + (4513078399/10000000000 : ℝ)*x 1 + (2124183673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378673959/10000000000 : ℝ)^2059 ≤ (33315031375347/100000000000000 : ℝ)^1547 := by
    have hnat : (4378673959 : ℕ)^2059*100000000000000^1547 ≤ 33315031375347^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378673959 10000000000 33315031375347 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513078399/10000000000 : ℝ)^2059 ≤ (34682958133237/100000000000000 : ℝ)^1547 := by
    have hnat : (4513078399 : ℕ)^2059*100000000000000^1547 ≤ 34682958133237^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513078399 10000000000 34682958133237 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124183673/5000000000 : ℝ)^2059 ≤ (32002010471391/100000000000000 : ℝ)^1547 := by
    have hnat : (2124183673 : ℕ)^2059*100000000000000^1547 ≤ 32002010471391^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124183673 5000000000 32002010471391 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378673959/10000000000 : ℝ), (4513078399/10000000000 : ℝ), (2124183673/5000000000 : ℝ)] ![(33315031375347/100000000000000 : ℝ), (34682958133237/100000000000000 : ℝ), (32002010471391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378673959/10000000000 : ℝ)|^2059 ≤ (33315031375347/100000000000000 : ℝ)^1547
        have hw : |(4378673959/10000000000 : ℝ)|=(4378673959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513078399/10000000000 : ℝ)|^2059 ≤ (34682958133237/100000000000000 : ℝ)^1547
        have hw : |(4513078399/10000000000 : ℝ)|=(4513078399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124183673/5000000000 : ℝ)|^2059 ≤ (32002010471391/100000000000000 : ℝ)^1547
        have hw : |(2124183673/5000000000 : ℝ)|=(2124183673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11161/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2743/25000 : ℝ) ^ (8235/2048 : ℝ) ≤ (2767087815826109/20000000000000000000 : ℝ) := by
    have hpowers : (2743/25000 : ℝ)^8235 ≤ (2767087815826109/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2743 : ℕ)^8235*20000000000000000000^2048 ≤ 2767087815826109^2048*25000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2743 25000 2767087815826109 20000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2743/25000 : ℝ)) (X := (2767087815826109/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/12500 : ℝ) ^ (8235/2048 : ℝ) ≤ (19779611985686187/50000000000000000000 : ℝ) := by
    have hpowers : (1781/12500 : ℝ)^8235 ≤ (19779611985686187/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1781 : ℕ)^8235*50000000000000000000^2048 ≤ 19779611985686187^2048*12500^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 12500 19779611985686187 50000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/12500 : ℝ)) (X := (19779611985686187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002767087815826109/10000000000000000000 : ℝ) ≤ (400027523530677/400000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (10002767087815826109/10000000000000000000 : ℝ)^2048 ≤ (400027523530677/400000000000000 : ℝ)^8235 := by
      have hnat : (10002767087815826109 : ℕ)^2048*400000000000000^8235 ≤ 400027523530677^8235*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002767087815826109 10000000000000000000 400027523530677 400000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400027523530677/400000000000000 : ℝ)) (X := (10002767087815826109/10000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053394663050502919/100000000000000000000 : ℝ) ≤ (80010621041219/80000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (100053394663050502919/100000000000000000000 : ℝ)^2048 ≤ (80010621041219/80000000000000 : ℝ)^8235 := by
      have hnat : (100053394663050502919 : ℕ)^2048*80000000000000^8235 ≤ 80010621041219^8235*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053394663050502919 100000000000000000000 80010621041219 80000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80010621041219/80000000000000 : ℝ)) (X := (100053394663050502919/100000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019779611985686187/25000000000000000000 : ℝ) ≤ (400078686881513/400000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (25019779611985686187/25000000000000000000 : ℝ)^2048 ≤ (400078686881513/400000000000000 : ℝ)^8235 := by
      have hnat : (25019779611985686187 : ℕ)^2048*400000000000000^8235 ≤ 400078686881513^8235*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019779611985686187 25000000000000000000 400078686881513 400000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400078686881513/400000000000000 : ℝ)) (X := (25019779611985686187/25000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2767087815826109/20000000000000000000 : ℝ) ≤ ((5038187703081251/5040000000000000 : ℝ)+2*(983910593/504000000000 : ℝ)*(2743/25000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (5038187703081251/5040000000000000 : ℝ)+2*(983910593/504000000000 : ℝ)*(2743/25000 : ℝ)=(400027523530677/400000000000000 : ℝ) by norm_num, show 1+2*(2767087815826109/20000000000000000000 : ℝ)=(10002767087815826109/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19779611985686187/50000000000000000000 : ℝ)+(2767087815826109/20000000000000000000 : ℝ) ≤ ((5038187703081251/5040000000000000 : ℝ)+(983910593/504000000000 : ℝ)*((1781/12500 : ℝ)+(2743/25000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (5038187703081251/5040000000000000 : ℝ)+(983910593/504000000000 : ℝ)*((1781/12500 : ℝ)+(2743/25000 : ℝ))=(80010621041219/80000000000000 : ℝ) by norm_num, show 1+(19779611985686187/50000000000000000000 : ℝ)+(2767087815826109/20000000000000000000 : ℝ)=(100053394663050502919/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19779611985686187/50000000000000000000 : ℝ) ≤ ((5038187703081251/5040000000000000 : ℝ)+2*(983910593/504000000000 : ℝ)*(1781/12500 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (5038187703081251/5040000000000000 : ℝ)+2*(983910593/504000000000 : ℝ)*(1781/12500 : ℝ)=(400078686881513/400000000000000 : ℝ) by norm_num, show 1+2*(19779611985686187/50000000000000000000 : ℝ)=(25019779611985686187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5038187703081251/5040000000000000 : ℝ)*(X 1 0+X 2 0)+(983910593/504000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (5038187703081251/5040000000000000 : ℝ)) (alpha := (983910593/504000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5038187703081251/5040000000000000 : ℝ)*(X 0 1+X 2 1)+(983910593/504000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (5038187703081251/5040000000000000 : ℝ)) (alpha := (983910593/504000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5038187703081251/5040000000000000 : ℝ)*(X 0 2+X 1 2)+(983910593/504000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (5038187703081251/5040000000000000 : ℝ)) (alpha := (983910593/504000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2214884767/10000000000 : ℝ)*X 0 0+(42169327/78125000 : ℝ)*X 0 1+(2630637429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345753867/10000000000 : ℝ)*X 1 0+(-456827933/2000000000 : ℝ)*X 1 1+(5261274823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672876941/5000000000 : ℝ)*X 2 0+(526127483/1000000000 : ℝ)*X 2 1+(-571034909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378662577/10000000000 : ℝ)*X 0 0+(4247670091/10000000000 : ℝ)*X 0 1+(4513773077/10000000000 : ℝ)*X 0 2+(4378662577/10000000000 : ℝ)*X 1 0+(4247670091/10000000000 : ℝ)*X 1 1+(4513773077/10000000000 : ℝ)*X 1 2+(4378662577/10000000000 : ℝ)*X 2 0+(4247670091/10000000000 : ℝ)*X 2 1+(4513773077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221489059/1000000000 : ℝ)*X 0 0+(5261630943/10000000000 : ℝ)*X 0 1+(539731643/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062292309/2000000000 : ℝ)*X 1 0+(-2148098083/10000000000 : ℝ)*X 1 1+(2698658217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311461549/10000000000 : ℝ)*X 2 0+(5397316439/10000000000 : ℝ)*X 2 1+(-2148098071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378673959/10000000000 : ℝ)*X 0 0+(4513078399/10000000000 : ℝ)*X 0 1+(2124183673/5000000000 : ℝ)*X 0 2+(4378673959/10000000000 : ℝ)*X 1 0+(4513078399/10000000000 : ℝ)*X 1 1+(2124183673/5000000000 : ℝ)*X 1 2+(4378673959/10000000000 : ℝ)*X 2 0+(4513078399/10000000000 : ℝ)*X 2 1+(2124183673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (322099200602170448679343/84000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (264293/31250000000 : ℝ)*(base19) + (414119039/50000000000000 : ℝ)*(base23) + (5088007/25000000000000 : ℝ)*(lower2) + (31955133/50000000000000 : ℝ)*(upper3) + (16592263/20000000000000 : ℝ)*(upper5) + (5544720967276453/100000000000000 : ℝ)*(major0) + (5544720967276453/100000000000000 : ℝ)*(major1) + (2772360483638227/50000000000000 : ℝ)*(major2) + (7331453283495037/100000000000000 : ℝ)*(sp0) + (1832868828304753/25000000000000 : ℝ)*(sp1) + (3665737665359267/50000000000000 : ℝ)*(sp2) + (939488650954139/25000000000000 : ℝ)*(sp3) + (915018463/4000000000000 : ℝ)*(sp4) + (5521981293/50000000000000 : ℝ)*(sp7) + (3757965647779143/100000000000000 : ℝ)*(f.failure) + (1832869039739153/25000000000000 : ℝ)*(f.sum) + (28808422701/28000000000000000000000000 : ℝ)*base66 + (627446986524901/168000000000000000000000000000 : ℝ)*base67 + (433811563199659/84000000000000000000000000000 : ℝ)*base69 + (1816964417819099/168000000000000000000000000000 : ℝ)*base72 + (43529217131/5600000000000000000000000 : ℝ)*base73 + (2130319421279659/84000000000000000000000000000 : ℝ)*base75 + (908351130276703/504000000000000000000000000000 : ℝ)*base77 + (461034066852703/504000000000000000000000000000 : ℝ)*base79 + (205848475799/126000000000000000000000000 : ℝ)*base82 + (1621741/10000000000000000000000 : ℝ)*base90 + (1621741/10000000000000000000000 : ℝ)*base92 + (101621741/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19564083307435476424593/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1837749541/100000000000000 : ℝ)*(base19) + (50244259/2500000000000 : ℝ)*(base23) + (205363689/100000000000000 : ℝ)*(upper3) + (72462383/100000000000000 : ℝ)*(lower4) + (49618923/25000000000000 : ℝ)*(upper5) + (5573843466483297/100000000000000 : ℝ)*(major0) + (5573843466483297/100000000000000 : ℝ)*(major1) + (5573843466483297/100000000000000 : ℝ)*(major2) + (23648730033/50000000000000 : ℝ)*(sp1) + (51950911313/100000000000000 : ℝ)*(sp2) + (1842495755599187/25000000000000 : ℝ)*(sp4) + (3684966943593571/50000000000000 : ℝ)*(sp5) + (294797162468603/4000000000000 : ℝ)*(sp6) + (1888851792250891/50000000000000 : ℝ)*(sp7) + (1888851792250891/50000000000000 : ℝ)*(f.failure) + (1842495755599187/25000000000000 : ℝ)*(f.sum) + (95216023421/42000000000000000000000000 : ℝ)*base66 + (1396642321348849/168000000000000000000000000000 : ℝ)*base67 + (15816749908849/168000000000000000000000000000 : ℝ)*base69 + (27754101124849/168000000000000000000000000000 : ℝ)*base71 + (216258214171/42000000000000000000000000 : ℝ)*base73 + (908763578500849/168000000000000000000000000000 : ℝ)*base75 + (596296788547151/168000000000000000000000000000 : ℝ)*base78 + (2206167734380849/168000000000000000000000000000 : ℝ)*base79 + (136531194983/42000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (37430617/5000000000000000000000 : ℝ)*base90 + (37430617/5000000000000000000000 : ℝ)*base92 + (37430617/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1043_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1043_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1043_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1043_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
