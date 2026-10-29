-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1658_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:16.335928+00:00
-- url     : https://prove2.me/submissions/9a2988f2-d46b-4c7c-8e2a-c675e1038ea4

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
theorem support_rectangle_w1658_s3_0 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1590500917/10000000000 : ℝ)*x 0 + (5445231781/10000000000 : ℝ)*x 1 + (5184358023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590500917/10000000000 : ℝ)^4951 ≤ (4923759516269/50000000000000 : ℝ)^3927 := by
    have hnat : (1590500917 : ℕ)^4951*50000000000000^3927 ≤ 4923759516269^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590500917 10000000000 4923759516269 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445231781/10000000000 : ℝ)^4951 ≤ (9294163301687/20000000000000 : ℝ)^3927 := by
    have hnat : (5445231781 : ℕ)^4951*20000000000000^3927 ≤ 9294163301687^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445231781 10000000000 9294163301687 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184358023/10000000000 : ℝ)^4951 ≤ (43681664445067/100000000000000 : ℝ)^3927 := by
    have hnat : (5184358023 : ℕ)^4951*100000000000000^3927 ≤ 43681664445067^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184358023 10000000000 43681664445067 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1590500917/10000000000 : ℝ), (5445231781/10000000000 : ℝ), (5184358023/10000000000 : ℝ)] ![(4923759516269/50000000000000 : ℝ), (9294163301687/20000000000000 : ℝ), (43681664445067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1590500917/10000000000 : ℝ)|^4951 ≤ (4923759516269/50000000000000 : ℝ)^3927
        have hw : |(-1590500917/10000000000 : ℝ)|=(1590500917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445231781/10000000000 : ℝ)|^4951 ≤ (9294163301687/20000000000000 : ℝ)^3927
        have hw : |(5445231781/10000000000 : ℝ)|=(5445231781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184358023/10000000000 : ℝ)|^4951 ≤ (43681664445067/100000000000000 : ℝ)^3927
        have hw : |(5184358023/10000000000 : ℝ)|=(5184358023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_1 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346547637/10000000000 : ℝ)*x 0 + (-344951047/2000000000 : ℝ)*x 1 + (5184357921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346547637/10000000000 : ℝ)^4951 ≤ (1419110474949/3125000000000 : ℝ)^3927 := by
    have hnat : (5346547637 : ℕ)^4951*3125000000000^3927 ≤ 1419110474949^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346547637 10000000000 1419110474949 3125000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344951047/2000000000 : ℝ)^4951 ≤ (10906801416503/100000000000000 : ℝ)^3927 := by
    have hnat : (344951047 : ℕ)^4951*100000000000000^3927 ≤ 10906801416503^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344951047 2000000000 10906801416503 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184357921/10000000000 : ℝ)^4951 ≤ (10920415840387/25000000000000 : ℝ)^3927 := by
    have hnat : (5184357921 : ℕ)^4951*25000000000000^3927 ≤ 10920415840387^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184357921 10000000000 10920415840387 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346547637/10000000000 : ℝ), (-344951047/2000000000 : ℝ), (5184357921/10000000000 : ℝ)] ![(1419110474949/3125000000000 : ℝ), (10906801416503/100000000000000 : ℝ), (10920415840387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346547637/10000000000 : ℝ)|^4951 ≤ (1419110474949/3125000000000 : ℝ)^3927
        have hw : |(5346547637/10000000000 : ℝ)|=(5346547637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344951047/2000000000 : ℝ)|^4951 ≤ (10906801416503/100000000000000 : ℝ)^3927
        have hw : |(-344951047/2000000000 : ℝ)|=(344951047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184357921/10000000000 : ℝ)|^4951 ≤ (10920415840387/25000000000000 : ℝ)^3927
        have hw : |(5184357921/10000000000 : ℝ)|=(5184357921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_2 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346547601/10000000000 : ℝ)*x 0 + (5184357773/10000000000 : ℝ)*x 1 + (-862377741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346547601/10000000000 : ℝ)^4951 ≤ (9082306962573/20000000000000 : ℝ)^3927 := by
    have hnat : (5346547601 : ℕ)^4951*20000000000000^3927 ≤ 9082306962573^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346547601 10000000000 9082306962573 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184357773/10000000000 : ℝ)^4951 ≤ (5460207723673/12500000000000 : ℝ)^3927 := by
    have hnat : (5184357773 : ℕ)^4951*12500000000000^3927 ≤ 5460207723673^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184357773 10000000000 5460207723673 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862377741/5000000000 : ℝ)^4951 ≤ (2181360677149/20000000000000 : ℝ)^3927 := by
    have hnat : (862377741 : ℕ)^4951*20000000000000^3927 ≤ 2181360677149^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862377741 5000000000 2181360677149 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346547601/10000000000 : ℝ), (5184357773/10000000000 : ℝ), (-862377741/5000000000 : ℝ)] ![(9082306962573/20000000000000 : ℝ), (5460207723673/12500000000000 : ℝ), (2181360677149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346547601/10000000000 : ℝ)|^4951 ≤ (9082306962573/20000000000000 : ℝ)^3927
        have hw : |(5346547601/10000000000 : ℝ)|=(5346547601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184357773/10000000000 : ℝ)|^4951 ≤ (5460207723673/12500000000000 : ℝ)^3927
        have hw : |(5184357773/10000000000 : ℝ)|=(5184357773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-862377741/5000000000 : ℝ)|^4951 ≤ (2181360677149/20000000000000 : ℝ)^3927
        have hw : |(-862377741/5000000000 : ℝ)|=(862377741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_3 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26091437/62500000 : ℝ)*x 0 + (768746021/2000000000 : ℝ)*x 1 + (4525483087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26091437/62500000 : ℝ)^4951 ≤ (33242276913867/100000000000000 : ℝ)^3927 := by
    have hnat : (26091437 : ℕ)^4951*100000000000000^3927 ≤ 33242276913867^3927*62500000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26091437 62500000 33242276913867 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768746021/2000000000 : ℝ)^4951 ≤ (29955289803169/100000000000000 : ℝ)^3927 := by
    have hnat : (768746021 : ℕ)^4951*100000000000000^3927 ≤ 29955289803169^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768746021 2000000000 29955289803169 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525483087/10000000000 : ℝ)^4951 ≤ (18401216632093/50000000000000 : ℝ)^3927 := by
    have hnat : (4525483087 : ℕ)^4951*50000000000000^3927 ≤ 18401216632093^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525483087 10000000000 18401216632093 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26091437/62500000 : ℝ), (768746021/2000000000 : ℝ), (4525483087/10000000000 : ℝ)] ![(33242276913867/100000000000000 : ℝ), (29955289803169/100000000000000 : ℝ), (18401216632093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26091437/62500000 : ℝ)|^4951 ≤ (33242276913867/100000000000000 : ℝ)^3927
        have hw : |(26091437/62500000 : ℝ)|=(26091437/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(768746021/2000000000 : ℝ)|^4951 ≤ (29955289803169/100000000000000 : ℝ)^3927
        have hw : |(768746021/2000000000 : ℝ)|=(768746021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525483087/10000000000 : ℝ)|^4951 ≤ (18401216632093/50000000000000 : ℝ)^3927
        have hw : |(4525483087/10000000000 : ℝ)|=(4525483087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_4 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1590564469/10000000000 : ℝ)*x 0 + (5186339663/10000000000 : ℝ)*x 1 + (680403631/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590564469/10000000000 : ℝ)^4951 ≤ (4924007558951/50000000000000 : ℝ)^3927 := by
    have hnat : (1590564469 : ℕ)^4951*50000000000000^3927 ≤ 4924007558951^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590564469 10000000000 4924007558951 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186339663/10000000000 : ℝ)^4951 ≤ (4370271592433/10000000000000 : ℝ)^3927 := by
    have hnat : (5186339663 : ℕ)^4951*10000000000000^3927 ≤ 4370271592433^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186339663 10000000000 4370271592433 10000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680403631/1250000000 : ℝ)^4951 ≤ (1857970757769/4000000000000 : ℝ)^3927 := by
    have hnat : (680403631 : ℕ)^4951*4000000000000^3927 ≤ 1857970757769^3927*1250000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680403631 1250000000 1857970757769 4000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1590564469/10000000000 : ℝ), (5186339663/10000000000 : ℝ), (680403631/1250000000 : ℝ)] ![(4924007558951/50000000000000 : ℝ), (4370271592433/10000000000000 : ℝ), (1857970757769/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1590564469/10000000000 : ℝ)|^4951 ≤ (4924007558951/50000000000000 : ℝ)^3927
        have hw : |(-1590564469/10000000000 : ℝ)|=(1590564469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186339663/10000000000 : ℝ)|^4951 ≤ (4370271592433/10000000000000 : ℝ)^3927
        have hw : |(5186339663/10000000000 : ℝ)|=(5186339663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680403631/1250000000 : ℝ)|^4951 ≤ (1857970757769/4000000000000 : ℝ)^3927
        have hw : |(680403631/1250000000 : ℝ)|=(680403631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_5 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276790733/10000000000 : ℝ)*x 0 + (-183235547/1250000000 : ℝ)*x 1 + (2721614533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276790733/10000000000 : ℝ)^4951 ≤ (2791614052321/6250000000000 : ℝ)^3927 := by
    have hnat : (5276790733 : ℕ)^4951*6250000000000^3927 ≤ 2791614052321^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276790733 10000000000 2791614052321 6250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183235547/1250000000 : ℝ)^4951 ≤ (8884906006059/100000000000000 : ℝ)^3927 := by
    have hnat : (183235547 : ℕ)^4951*100000000000000^3927 ≤ 8884906006059^3927*1250000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183235547 1250000000 8884906006059 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721614533/5000000000 : ℝ)^4951 ≤ (46449269137879/100000000000000 : ℝ)^3927 := by
    have hnat : (2721614533 : ℕ)^4951*100000000000000^3927 ≤ 46449269137879^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721614533 5000000000 46449269137879 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276790733/10000000000 : ℝ), (-183235547/1250000000 : ℝ), (2721614533/5000000000 : ℝ)] ![(2791614052321/6250000000000 : ℝ), (8884906006059/100000000000000 : ℝ), (46449269137879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276790733/10000000000 : ℝ)|^4951 ≤ (2791614052321/6250000000000 : ℝ)^3927
        have hw : |(5276790733/10000000000 : ℝ)|=(5276790733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183235547/1250000000 : ℝ)|^4951 ≤ (8884906006059/100000000000000 : ℝ)^3927
        have hw : |(-183235547/1250000000 : ℝ)|=(183235547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721614533/5000000000 : ℝ)|^4951 ≤ (46449269137879/100000000000000 : ℝ)^3927
        have hw : |(2721614533/5000000000 : ℝ)|=(2721614533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_6 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1688573/3200000 : ℝ)*x 0 + (1360807293/2500000000 : ℝ)*x 1 + (-732942189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1688573/3200000 : ℝ)^4951 ≤ (22332911842291/50000000000000 : ℝ)^3927 := by
    have hnat : (1688573 : ℕ)^4951*50000000000000^3927 ≤ 22332911842291^3927*3200000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688573 3200000 22332911842291 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360807293/2500000000 : ℝ)^4951 ≤ (46449270278287/100000000000000 : ℝ)^3927 := by
    have hnat : (1360807293 : ℕ)^4951*100000000000000^3927 ≤ 46449270278287^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360807293 2500000000 46449270278287 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732942189/5000000000 : ℝ)^4951 ≤ (4442453010671/50000000000000 : ℝ)^3927 := by
    have hnat : (732942189 : ℕ)^4951*50000000000000^3927 ≤ 4442453010671^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732942189 5000000000 4442453010671 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1688573/3200000 : ℝ), (1360807293/2500000000 : ℝ), (-732942189/5000000000 : ℝ)] ![(22332911842291/50000000000000 : ℝ), (46449270278287/100000000000000 : ℝ), (4442453010671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1688573/3200000 : ℝ)|^4951 ≤ (22332911842291/50000000000000 : ℝ)^3927
        have hw : |(1688573/3200000 : ℝ)|=(1688573/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360807293/2500000000 : ℝ)|^4951 ≤ (46449270278287/100000000000000 : ℝ)^3927
        have hw : |(1360807293/2500000000 : ℝ)|=(1360807293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-732942189/5000000000 : ℝ)|^4951 ≤ (4442453010671/50000000000000 : ℝ)^3927
        have hw : |(-732942189/5000000000 : ℝ)|=(732942189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s3_7 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130462359/312500000 : ℝ)*x 0 + (4520304057/10000000000 : ℝ)*x 1 + (481120437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130462359/312500000 : ℝ)^4951 ≤ (2077746194659/6250000000000 : ℝ)^3927 := by
    have hnat : (130462359 : ℕ)^4951*6250000000000^3927 ≤ 2077746194659^3927*312500000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130462359 312500000 2077746194659 6250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520304057/10000000000 : ℝ)^4951 ≤ (9187335373187/25000000000000 : ℝ)^3927 := by
    have hnat : (4520304057 : ℕ)^4951*25000000000000^3927 ≤ 9187335373187^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520304057 10000000000 9187335373187 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481120437/1250000000 : ℝ)^4951 ≤ (30006719375207/100000000000000 : ℝ)^3927 := by
    have hnat : (481120437 : ℕ)^4951*100000000000000^3927 ≤ 30006719375207^3927*1250000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481120437 1250000000 30006719375207 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130462359/312500000 : ℝ), (4520304057/10000000000 : ℝ), (481120437/1250000000 : ℝ)] ![(2077746194659/6250000000000 : ℝ), (9187335373187/25000000000000 : ℝ), (30006719375207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130462359/312500000 : ℝ)|^4951 ≤ (2077746194659/6250000000000 : ℝ)^3927
        have hw : |(130462359/312500000 : ℝ)|=(130462359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520304057/10000000000 : ℝ)|^4951 ≤ (9187335373187/25000000000000 : ℝ)^3927
        have hw : |(4520304057/10000000000 : ℝ)|=(4520304057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481120437/1250000000 : ℝ)|^4951 ≤ (30006719375207/100000000000000 : ℝ)^3927
        have hw : |(481120437/1250000000 : ℝ)|=(481120437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1658_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2677/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (508/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (102/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (102/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (102/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (102/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (102/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (102/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (213/2000 : ℝ) ^ (4947/1024 : ℝ) ≤ (500049240532857/25000000000000000000 : ℝ) := by
    have hpowers : (213/2000 : ℝ)^4947 ≤ (500049240532857/25000000000000000000 : ℝ)^1024 := by
      have hnat : (213 : ℕ)^4947*25000000000000000000^1024 ≤ 500049240532857^1024*2000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        213 2000 500049240532857 25000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (213/2000 : ℝ)) (X := (500049240532857/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (102/625 : ℝ) ^ (4947/1024 : ℝ) ≤ (15725628495849589/100000000000000000000 : ℝ) := by
    have hpowers : (102/625 : ℝ)^4947 ≤ (15725628495849589/100000000000000000000 : ℝ)^1024 := by
      have hnat : (102 : ℕ)^4947*100000000000000000000^1024 ≤ 15725628495849589^1024*625^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102 625 15725628495849589 100000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (102/625 : ℝ)) (X := (15725628495849589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500500049240532857/12500000000000000000 : ℝ) ≤ (10000082804495739/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (12500500049240532857/12500000000000000000 : ℝ)^1024 ≤ (10000082804495739/10000000000000000 : ℝ)^4947 := by
      have hnat : (12500500049240532857 : ℕ)^1024*10000000000000000^4947 ≤ 10000082804495739^4947*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500500049240532857 12500000000000000000 10000082804495739 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000082804495739/10000000000000000 : ℝ)) (X := (12500500049240532857/12500000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017725825457981017/100000000000000000000 : ℝ) ≤ (2500091722102651/2500000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (100017725825457981017/100000000000000000000 : ℝ)^1024 ≤ (2500091722102651/2500000000000000 : ℝ)^4947 := by
      have hnat : (100017725825457981017 : ℕ)^1024*2500000000000000^4947 ≤ 2500091722102651^4947*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017725825457981017 100000000000000000000 2500091722102651 2500000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500091722102651/2500000000000000 : ℝ)) (X := (100017725825457981017/100000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015725628495849589/50000000000000000000 : ℝ) ≤ (10000650972325469/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (50015725628495849589/50000000000000000000 : ℝ)^1024 ≤ (10000650972325469/10000000000000000 : ℝ)^4947 := by
      have hnat : (50015725628495849589 : ℕ)^1024*10000000000000000^4947 ≤ 10000650972325469^4947*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015725628495849589 50000000000000000000 10000650972325469 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650972325469/10000000000000000 : ℝ)) (X := (50015725628495849589/50000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(500049240532857/25000000000000000000 : ℝ) ≤ ((1889813950470140521/1890000000000000000 : ℝ)+2*(56816782973/113400000000000 : ℝ)*(213/2000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (1889813950470140521/1890000000000000000 : ℝ)+2*(56816782973/113400000000000 : ℝ)*(213/2000 : ℝ)=(10000082804495739/10000000000000000 : ℝ) by norm_num, show 1+2*(500049240532857/25000000000000000000 : ℝ)=(12500500049240532857/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15725628495849589/100000000000000000000 : ℝ)+(500049240532857/25000000000000000000 : ℝ) ≤ ((1889813950470140521/1890000000000000000 : ℝ)+(56816782973/113400000000000 : ℝ)*((102/625 : ℝ)+(213/2000 : ℝ)))^(4947/1024 : ℝ) := by
    rw [show (1889813950470140521/1890000000000000000 : ℝ)+(56816782973/113400000000000 : ℝ)*((102/625 : ℝ)+(213/2000 : ℝ))=(2500091722102651/2500000000000000 : ℝ) by norm_num, show 1+(15725628495849589/100000000000000000000 : ℝ)+(500049240532857/25000000000000000000 : ℝ)=(100017725825457981017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15725628495849589/100000000000000000000 : ℝ) ≤ ((1889813950470140521/1890000000000000000 : ℝ)+2*(56816782973/113400000000000 : ℝ)*(102/625 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (1889813950470140521/1890000000000000000 : ℝ)+2*(56816782973/113400000000000 : ℝ)*(102/625 : ℝ)=(10000650972325469/10000000000000000 : ℝ) by norm_num, show 1+2*(15725628495849589/100000000000000000000 : ℝ)=(50015725628495849589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1889813950470140521/1890000000000000000 : ℝ)*(X 1 0+X 2 0)+(56816782973/113400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (102/625 : ℝ)) (c := (1889813950470140521/1890000000000000000 : ℝ)) (alpha := (56816782973/113400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1889813950470140521/1890000000000000000 : ℝ)*(X 0 1+X 2 1)+(56816782973/113400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (102/625 : ℝ)) (c := (1889813950470140521/1890000000000000000 : ℝ)) (alpha := (56816782973/113400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1889813950470140521/1890000000000000000 : ℝ)*(X 0 2+X 1 2)+(56816782973/113400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (102/625 : ℝ)) (c := (1889813950470140521/1890000000000000000 : ℝ)) (alpha := (56816782973/113400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1590500917/10000000000 : ℝ)*X 0 0+(5445231781/10000000000 : ℝ)*X 0 1+(5184358023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346547637/10000000000 : ℝ)*X 1 0+(-344951047/2000000000 : ℝ)*X 1 1+(5184357921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346547601/10000000000 : ℝ)*X 2 0+(5184357773/10000000000 : ℝ)*X 2 1+(-862377741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((26091437/62500000 : ℝ)*X 0 0+(768746021/2000000000 : ℝ)*X 0 1+(4525483087/10000000000 : ℝ)*X 0 2+(26091437/62500000 : ℝ)*X 1 0+(768746021/2000000000 : ℝ)*X 1 1+(4525483087/10000000000 : ℝ)*X 1 2+(26091437/62500000 : ℝ)*X 2 0+(768746021/2000000000 : ℝ)*X 2 1+(4525483087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1590564469/10000000000 : ℝ)*X 0 0+(5186339663/10000000000 : ℝ)*X 0 1+(680403631/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276790733/10000000000 : ℝ)*X 1 0+(-183235547/1250000000 : ℝ)*X 1 1+(2721614533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1688573/3200000 : ℝ)*X 2 0+(1360807293/2500000000 : ℝ)*X 2 1+(-732942189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((130462359/312500000 : ℝ)*X 0 0+(4520304057/10000000000 : ℝ)*X 0 1+(481120437/1250000000 : ℝ)*X 0 2+(130462359/312500000 : ℝ)*X 1 0+(4520304057/10000000000 : ℝ)*X 1 1+(481120437/1250000000 : ℝ)*X 1 2+(130462359/312500000 : ℝ)*X 2 0+(4520304057/10000000000 : ℝ)*X 2 1+(481120437/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1502287668448033347021251/421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483178103/100000000000000 : ℝ)*(base19) + (58200149/10000000000000 : ℝ)*(base23) + (3913967/50000000000000 : ℝ)*(upper3) + (39286653/50000000000000 : ℝ)*(lower4) + (10351760130467/390625000000 : ℝ)*(major0) + (10351760130467/390625000000 : ℝ)*(major1) + (10351760130467/390625000000 : ℝ)*(major2) + (1916640218676711/50000000000000 : ℝ)*(sp0) + (1916643564855233/50000000000000 : ℝ)*(sp1) + (3833285319649191/100000000000000 : ℝ)*(sp2) + (146681035710939/10000000000000 : ℝ)*(sp3) + (3587767573/50000000000000 : ℝ)*(sp4) + (6684523/390625000000 : ℝ)*(sp6) + (3098101869/100000000000000 : ℝ)*(sp7) + (1466813455211259/100000000000000 : ℝ)*(f.failure) + (479160951611071/12500000000000 : ℝ)*(f.sum) + (3117053357/50625000000000000000000000 : ℝ)*base66 + (6696304686828437/1265625000000000000000000000000 : ℝ)*base67 + (112268025148457/79101562500000000000000000000 : ℝ)*base69 + (785388937296719/632812500000000000000000000000 : ℝ)*base72 + (46514239201/405000000000000000000000000 : ℝ)*base74 + (255494650644541/39550781250000000000000000000 : ℝ)*base75 + (2025607997546563/1265625000000000000000000000000 : ℝ)*base78 + (2567590781547031/632812500000000000000000000000 : ℝ)*base79 + (363558701869/101250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (476413/5000000000000000000000 : ℝ)*base90 + (476413/5000000000000000000000 : ℝ)*base92 + (476413/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2638934265288130506078923/337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221697043/20000000000000 : ℝ)*(base19) + (546508649/50000000000000 : ℝ)*(base23) + (185189957/100000000000000 : ℝ)*(upper3) + (12662381/50000000000000 : ℝ)*(lower4) + (35834663/25000000000000 : ℝ)*(upper5) + (134557040978047/5000000000000 : ℝ)*(major0) + (134557040978047/5000000000000 : ℝ)*(major1) + (134557040978047/5000000000000 : ℝ)*(major2) + (6314498063/50000000000000 : ℝ)*(sp1) + (1731914959/12500000000000 : ℝ)*(sp2) + (973181080258873/25000000000000 : ℝ)*(sp4) + (77854211671083/2000000000000 : ℝ)*(sp5) + (1946354686349261/50000000000000 : ℝ)*(sp6) + (744778528725449/50000000000000 : ℝ)*(sp7) + (744778528725449/50000000000000 : ℝ)*(f.failure) + (973181080258873/25000000000000 : ℝ)*(f.sum) + (131015497957/56700000000000000000000000 : ℝ)*base65 + (191509569244722539/28350000000000000000000000000000 : ℝ)*base68 + (370108293745422539/28350000000000000000000000000000 : ℝ)*base70 + (133366045475622539/28350000000000000000000000000000 : ℝ)*base72 + (58966881667/56700000000000000000000000 : ℝ)*base73 + (98291360799077461/28350000000000000000000000000000 : ℝ)*base75 + (393888849874122539/28350000000000000000000000000000 : ℝ)*base78 + (102331101742122539/28350000000000000000000000000000 : ℝ)*base80 + (1067943007567/283500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (18708257/2500000000000000000000 : ℝ)*base89 + (18708257/2500000000000000000000 : ℝ)*base91 + (18708257/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1658_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (508/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1658_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1658_s4_0 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1590538259/10000000000 : ℝ)*x 0 + (5445040857/10000000000 : ℝ)*x 1 + (1036904793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590538259/10000000000 : ℝ)^4951 ≤ (4923905261327/50000000000000 : ℝ)^3927 := by
    have hnat : (1590538259 : ℕ)^4951*50000000000000^3927 ≤ 4923905261327^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590538259 10000000000 4923905261327 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445040857/10000000000 : ℝ)^4951 ≤ (46468762252753/100000000000000 : ℝ)^3927 := by
    have hnat : (5445040857 : ℕ)^4951*100000000000000^3927 ≤ 46468762252753^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445040857 10000000000 46468762252753 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036904793/2000000000 : ℝ)^4951 ≤ (10920856802447/25000000000000 : ℝ)^3927 := by
    have hnat : (1036904793 : ℕ)^4951*25000000000000^3927 ≤ 10920856802447^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036904793 2000000000 10920856802447 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1590538259/10000000000 : ℝ), (5445040857/10000000000 : ℝ), (1036904793/2000000000 : ℝ)] ![(4923905261327/50000000000000 : ℝ), (46468762252753/100000000000000 : ℝ), (10920856802447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1590538259/10000000000 : ℝ)|^4951 ≤ (4923905261327/50000000000000 : ℝ)^3927
        have hw : |(-1590538259/10000000000 : ℝ)|=(1590538259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445040857/10000000000 : ℝ)|^4951 ≤ (46468762252753/100000000000000 : ℝ)^3927
        have hw : |(5445040857/10000000000 : ℝ)|=(5445040857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036904793/2000000000 : ℝ)|^4951 ≤ (10920856802447/25000000000000 : ℝ)^3927
        have hw : |(1036904793/2000000000 : ℝ)|=(1036904793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_1 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673247873/5000000000 : ℝ)*x 0 + (-1724603763/10000000000 : ℝ)*x 1 + (648065489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673247873/5000000000 : ℝ)^4951 ≤ (45410979529253/100000000000000 : ℝ)^3927 := by
    have hnat : (2673247873 : ℕ)^4951*100000000000000^3927 ≤ 45410979529253^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673247873 5000000000 45410979529253 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724603763/10000000000 : ℝ)^4951 ≤ (2726398449787/25000000000000 : ℝ)^3927 := by
    have hnat : (1724603763 : ℕ)^4951*25000000000000^3927 ≤ 2726398449787^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724603763 10000000000 2726398449787 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648065489/1250000000 : ℝ)^4951 ≤ (43683426646779/100000000000000 : ℝ)^3927 := by
    have hnat : (648065489 : ℕ)^4951*100000000000000^3927 ≤ 43683426646779^3927*1250000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648065489 1250000000 43683426646779 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673247873/5000000000 : ℝ), (-1724603763/10000000000 : ℝ), (648065489/1250000000 : ℝ)] ![(45410979529253/100000000000000 : ℝ), (2726398449787/25000000000000 : ℝ), (43683426646779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673247873/5000000000 : ℝ)|^4951 ≤ (45410979529253/100000000000000 : ℝ)^3927
        have hw : |(2673247873/5000000000 : ℝ)|=(2673247873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724603763/10000000000 : ℝ)|^4951 ≤ (2726398449787/25000000000000 : ℝ)^3927
        have hw : |(-1724603763/10000000000 : ℝ)|=(1724603763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648065489/1250000000 : ℝ)|^4951 ≤ (43683426646779/100000000000000 : ℝ)^3927
        have hw : |(648065489/1250000000 : ℝ)|=(648065489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_2 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069299141/2000000000 : ℝ)*x 0 + (5184523959/10000000000 : ℝ)*x 1 + (-1724603757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069299141/2000000000 : ℝ)^4951 ≤ (45410979090209/100000000000000 : ℝ)^3927 := by
    have hnat : (1069299141 : ℕ)^4951*100000000000000^3927 ≤ 45410979090209^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069299141 2000000000 45410979090209 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184523959/10000000000 : ℝ)^4951 ≤ (10920856786513/25000000000000 : ℝ)^3927 := by
    have hnat : (5184523959 : ℕ)^4951*25000000000000^3927 ≤ 10920856786513^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184523959 10000000000 10920856786513 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724603757/10000000000 : ℝ)^4951 ≤ (10905593751313/100000000000000 : ℝ)^3927 := by
    have hnat : (1724603757 : ℕ)^4951*100000000000000^3927 ≤ 10905593751313^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724603757 10000000000 10905593751313 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069299141/2000000000 : ℝ), (5184523959/10000000000 : ℝ), (-1724603757/10000000000 : ℝ)] ![(45410979090209/100000000000000 : ℝ), (10920856786513/25000000000000 : ℝ), (10905593751313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069299141/2000000000 : ℝ)|^4951 ≤ (45410979090209/100000000000000 : ℝ)^3927
        have hw : |(1069299141/2000000000 : ℝ)|=(1069299141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184523959/10000000000 : ℝ)|^4951 ≤ (10920856786513/25000000000000 : ℝ)^3927
        have hw : |(5184523959/10000000000 : ℝ)|=(5184523959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1724603757/10000000000 : ℝ)|^4951 ≤ (10905593751313/100000000000000 : ℝ)^3927
        have hw : |(-1724603757/10000000000 : ℝ)|=(1724603757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_3 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174654973/10000000000 : ℝ)*x 0 + (3844193823/10000000000 : ℝ)*x 1 + (2262507077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174654973/10000000000 : ℝ)^4951 ≤ (33242528429443/100000000000000 : ℝ)^3927 := by
    have hnat : (4174654973 : ℕ)^4951*100000000000000^3927 ≤ 33242528429443^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174654973 10000000000 33242528429443 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3844193823/10000000000 : ℝ)^4951 ≤ (29959846115117/100000000000000 : ℝ)^3927 := by
    have hnat : (3844193823 : ℕ)^4951*100000000000000^3927 ≤ 29959846115117^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844193823 10000000000 29959846115117 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262507077/5000000000 : ℝ)^4951 ≤ (36797625440403/100000000000000 : ℝ)^3927 := by
    have hnat : (2262507077 : ℕ)^4951*100000000000000^3927 ≤ 36797625440403^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262507077 5000000000 36797625440403 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174654973/10000000000 : ℝ), (3844193823/10000000000 : ℝ), (2262507077/5000000000 : ℝ)] ![(33242528429443/100000000000000 : ℝ), (29959846115117/100000000000000 : ℝ), (36797625440403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174654973/10000000000 : ℝ)|^4951 ≤ (33242528429443/100000000000000 : ℝ)^3927
        have hw : |(4174654973/10000000000 : ℝ)|=(4174654973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3844193823/10000000000 : ℝ)|^4951 ≤ (29959846115117/100000000000000 : ℝ)^3927
        have hw : |(3844193823/10000000000 : ℝ)|=(3844193823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262507077/5000000000 : ℝ)|^4951 ≤ (36797625440403/100000000000000 : ℝ)^3927
        have hw : |(2262507077/5000000000 : ℝ)|=(2262507077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_4 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-318120199/2000000000 : ℝ)*x 0 + (5186500293/10000000000 : ℝ)*x 1 + (5443043927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (318120199/2000000000 : ℝ)^4951 ≤ (2462075060327/25000000000000 : ℝ)^3927 := by
    have hnat : (318120199 : ℕ)^4951*25000000000000^3927 ≤ 2462075060327^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318120199 2000000000 2462075060327 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186500293/10000000000 : ℝ)^4951 ≤ (21852211215341/50000000000000 : ℝ)^3927 := by
    have hnat : (5186500293 : ℕ)^4951*50000000000000^3927 ≤ 21852211215341^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186500293 10000000000 21852211215341 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443043927/10000000000 : ℝ)^4951 ≤ (46447277316971/100000000000000 : ℝ)^3927 := by
    have hnat : (5443043927 : ℕ)^4951*100000000000000^3927 ≤ 46447277316971^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443043927 10000000000 46447277316971 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-318120199/2000000000 : ℝ), (5186500293/10000000000 : ℝ), (5443043927/10000000000 : ℝ)] ![(2462075060327/25000000000000 : ℝ), (21852211215341/50000000000000 : ℝ), (46447277316971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-318120199/2000000000 : ℝ)|^4951 ≤ (2462075060327/25000000000000 : ℝ)^3927
        have hw : |(-318120199/2000000000 : ℝ)|=(318120199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186500293/10000000000 : ℝ)|^4951 ≤ (21852211215341/50000000000000 : ℝ)^3927
        have hw : |(5186500293/10000000000 : ℝ)|=(5186500293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443043927/10000000000 : ℝ)|^4951 ≤ (46447277316971/100000000000000 : ℝ)^3927
        have hw : |(5443043927/10000000000 : ℝ)|=(5443043927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_5 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319208587/2500000000 : ℝ)*x 0 + (-733041959/5000000000 : ℝ)*x 1 + (5443044069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319208587/2500000000 : ℝ)^4951 ≤ (22333145144009/50000000000000 : ℝ)^3927 := by
    have hnat : (1319208587 : ℕ)^4951*50000000000000^3927 ≤ 22333145144009^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319208587 2500000000 22333145144009 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733041959/5000000000 : ℝ)^4951 ≤ (4443215428119/50000000000000 : ℝ)^3927 := by
    have hnat : (733041959 : ℕ)^4951*50000000000000^3927 ≤ 4443215428119^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733041959 5000000000 4443215428119 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443044069/10000000000 : ℝ)^4951 ≤ (23223639422337/50000000000000 : ℝ)^3927 := by
    have hnat : (5443044069 : ℕ)^4951*50000000000000^3927 ≤ 23223639422337^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443044069 10000000000 23223639422337 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319208587/2500000000 : ℝ), (-733041959/5000000000 : ℝ), (5443044069/10000000000 : ℝ)] ![(22333145144009/50000000000000 : ℝ), (4443215428119/50000000000000 : ℝ), (23223639422337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319208587/2500000000 : ℝ)|^4951 ≤ (22333145144009/50000000000000 : ℝ)^3927
        have hw : |(1319208587/2500000000 : ℝ)|=(1319208587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-733041959/5000000000 : ℝ)|^4951 ≤ (4443215428119/50000000000000 : ℝ)^3927
        have hw : |(-733041959/5000000000 : ℝ)|=(733041959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443044069/10000000000 : ℝ)|^4951 ≤ (23223639422337/50000000000000 : ℝ)^3927
        have hw : |(5443044069/10000000000 : ℝ)|=(5443044069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_6 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276834303/10000000000 : ℝ)*x 0 + (5443044039/10000000000 : ℝ)*x 1 + (-1466084021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276834303/10000000000 : ℝ)^4951 ≤ (22333144903893/50000000000000 : ℝ)^3927 := by
    have hnat : (5276834303 : ℕ)^4951*50000000000000^3927 ≤ 22333144903893^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276834303 10000000000 22333144903893 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443044039/10000000000 : ℝ)^4951 ≤ (145147745381/312500000000 : ℝ)^3927 := by
    have hnat : (5443044039 : ℕ)^4951*312500000000^3927 ≤ 145147745381^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443044039 10000000000 145147745381 312500000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1466084021/10000000000 : ℝ)^4951 ≤ (1110803955419/12500000000000 : ℝ)^3927 := by
    have hnat : (1466084021 : ℕ)^4951*12500000000000^3927 ≤ 1110803955419^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466084021 10000000000 1110803955419 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276834303/10000000000 : ℝ), (5443044039/10000000000 : ℝ), (-1466084021/10000000000 : ℝ)] ![(22333144903893/50000000000000 : ℝ), (145147745381/312500000000 : ℝ), (1110803955419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276834303/10000000000 : ℝ)|^4951 ≤ (22333144903893/50000000000000 : ℝ)^3927
        have hw : |(5276834303/10000000000 : ℝ)|=(5276834303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443044039/10000000000 : ℝ)|^4951 ≤ (145147745381/312500000000 : ℝ)^3927
        have hw : |(5443044039/10000000000 : ℝ)|=(5443044039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1466084021/10000000000 : ℝ)|^4951 ≤ (1110803955419/12500000000000 : ℝ)^3927
        have hw : |(-1466084021/10000000000 : ℝ)|=(1466084021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_s4_7 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174819987/10000000000 : ℝ)*x 0 + (903969797/2000000000 : ℝ)*x 1 + (769882603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174819987/10000000000 : ℝ)^4951 ≤ (6648837014173/20000000000000 : ℝ)^3927 := by
    have hnat : (4174819987 : ℕ)^4951*20000000000000^3927 ≤ 6648837014173^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174819987 10000000000 6648837014173 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903969797/2000000000 : ℝ)^4951 ≤ (9186169293149/25000000000000 : ℝ)^3927 := by
    have hnat : (903969797 : ℕ)^4951*25000000000000^3927 ≤ 9186169293149^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903969797 2000000000 9186169293149 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769882603/2000000000 : ℝ)^4951 ≤ (3001113773843/10000000000000 : ℝ)^3927 := by
    have hnat : (769882603 : ℕ)^4951*10000000000000^3927 ≤ 3001113773843^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769882603 2000000000 3001113773843 10000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174819987/10000000000 : ℝ), (903969797/2000000000 : ℝ), (769882603/2000000000 : ℝ)] ![(6648837014173/20000000000000 : ℝ), (9186169293149/25000000000000 : ℝ), (3001113773843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174819987/10000000000 : ℝ)|^4951 ≤ (6648837014173/20000000000000 : ℝ)^3927
        have hw : |(4174819987/10000000000 : ℝ)|=(4174819987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903969797/2000000000 : ℝ)|^4951 ≤ (9186169293149/25000000000000 : ℝ)^3927
        have hw : |(903969797/2000000000 : ℝ)|=(903969797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(769882603/2000000000 : ℝ)|^4951 ≤ (3001113773843/10000000000000 : ℝ)^3927
        have hw : |(769882603/2000000000 : ℝ)|=(769882603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1658_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (508/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4063/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (508/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2677/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (508/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2677/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (508/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2677/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (508/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2677/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (508/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2677/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (508/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2677/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2677/25000 : ℝ) ^ (4947/1024 : ℝ) ≤ (51334347380547/2500000000000000000 : ℝ) := by
    have hpowers : (2677/25000 : ℝ)^4947 ≤ (51334347380547/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2677 : ℕ)^4947*2500000000000000000^1024 ≤ 51334347380547^1024*25000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2677 25000 51334347380547 2500000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2677/25000 : ℝ)) (X := (51334347380547/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (508/3125 : ℝ) ^ (4947/1024 : ℝ) ≤ (964370704467387/6250000000000000000 : ℝ) := by
    have hpowers : (508/3125 : ℝ)^4947 ≤ (964370704467387/6250000000000000000 : ℝ)^1024 := by
      have hnat : (508 : ℕ)^4947*6250000000000000000^1024 ≤ 964370704467387^1024*3125^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        508 3125 964370704467387 6250000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (508/3125 : ℝ)) (X := (964370704467387/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250051334347380547/1250000000000000000 : ℝ) ≤ (10000085005887659/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (1250051334347380547/1250000000000000000 : ℝ)^1024 ≤ (10000085005887659/10000000000000000 : ℝ)^4947 := by
      have hnat : (1250051334347380547 : ℕ)^1024*10000000000000000^4947 ≤ 10000085005887659^4947*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250051334347380547 1250000000000000000 10000085005887659 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000085005887659/10000000000000000 : ℝ)) (X := (1250051334347380547/1250000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502185413145837509/12500000000000000000 : ℝ) ≤ (2000072373816691/2000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (12502185413145837509/12500000000000000000 : ℝ)^1024 ≤ (2000072373816691/2000000000000000 : ℝ)^4947 := by
      have hnat : (12502185413145837509 : ℕ)^1024*2000000000000000^4947 ≤ 2000072373816691^4947*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502185413145837509 12500000000000000000 2000072373816691 2000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000072373816691/2000000000000000 : ℝ)) (X := (12502185413145837509/12500000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3125964370704467387/3125000000000000000 : ℝ) ≤ (10000638732279251/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (3125964370704467387/3125000000000000000 : ℝ)^1024 ≤ (10000638732279251/10000000000000000 : ℝ)^4947 := by
      have hnat : (3125964370704467387 : ℕ)^1024*10000000000000000^4947 ≤ 10000638732279251^4947*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125964370704467387 3125000000000000000 10000638732279251 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000638732279251/10000000000000000 : ℝ)) (X := (3125964370704467387/3125000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51334347380547/2500000000000000000 : ℝ) ≤ ((13868635577615891249/13870000000000000000 : ℝ)+2*(69215798949/138700000000000 : ℝ)*(2677/25000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (13868635577615891249/13870000000000000000 : ℝ)+2*(69215798949/138700000000000 : ℝ)*(2677/25000 : ℝ)=(10000085005887659/10000000000000000 : ℝ) by norm_num, show 1+2*(51334347380547/2500000000000000000 : ℝ)=(1250051334347380547/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(964370704467387/6250000000000000000 : ℝ)+(51334347380547/2500000000000000000 : ℝ) ≤ ((13868635577615891249/13870000000000000000 : ℝ)+(69215798949/138700000000000 : ℝ)*((508/3125 : ℝ)+(2677/25000 : ℝ)))^(4947/1024 : ℝ) := by
    rw [show (13868635577615891249/13870000000000000000 : ℝ)+(69215798949/138700000000000 : ℝ)*((508/3125 : ℝ)+(2677/25000 : ℝ))=(2000072373816691/2000000000000000 : ℝ) by norm_num, show 1+(964370704467387/6250000000000000000 : ℝ)+(51334347380547/2500000000000000000 : ℝ)=(12502185413145837509/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(964370704467387/6250000000000000000 : ℝ) ≤ ((13868635577615891249/13870000000000000000 : ℝ)+2*(69215798949/138700000000000 : ℝ)*(508/3125 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (13868635577615891249/13870000000000000000 : ℝ)+2*(69215798949/138700000000000 : ℝ)*(508/3125 : ℝ)=(10000638732279251/10000000000000000 : ℝ) by norm_num, show 1+2*(964370704467387/6250000000000000000 : ℝ)=(3125964370704467387/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13868635577615891249/13870000000000000000 : ℝ)*(X 1 0+X 2 0)+(69215798949/138700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (508/3125 : ℝ)) (c := (13868635577615891249/13870000000000000000 : ℝ)) (alpha := (69215798949/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13868635577615891249/13870000000000000000 : ℝ)*(X 0 1+X 2 1)+(69215798949/138700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (508/3125 : ℝ)) (c := (13868635577615891249/13870000000000000000 : ℝ)) (alpha := (69215798949/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13868635577615891249/13870000000000000000 : ℝ)*(X 0 2+X 1 2)+(69215798949/138700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (2677/25000 : ℝ)) (hi := (508/3125 : ℝ)) (c := (13868635577615891249/13870000000000000000 : ℝ)) (alpha := (69215798949/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1590538259/10000000000 : ℝ)*X 0 0+(5445040857/10000000000 : ℝ)*X 0 1+(1036904793/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673247873/5000000000 : ℝ)*X 1 0+(-1724603763/10000000000 : ℝ)*X 1 1+(648065489/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069299141/2000000000 : ℝ)*X 2 0+(5184523959/10000000000 : ℝ)*X 2 1+(-1724603757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4174654973/10000000000 : ℝ)*X 0 0+(3844193823/10000000000 : ℝ)*X 0 1+(2262507077/5000000000 : ℝ)*X 0 2+(4174654973/10000000000 : ℝ)*X 1 0+(3844193823/10000000000 : ℝ)*X 1 1+(2262507077/5000000000 : ℝ)*X 1 2+(4174654973/10000000000 : ℝ)*X 2 0+(3844193823/10000000000 : ℝ)*X 2 1+(2262507077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-318120199/2000000000 : ℝ)*X 0 0+(5186500293/10000000000 : ℝ)*X 0 1+(5443043927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319208587/2500000000 : ℝ)*X 1 0+(-733041959/5000000000 : ℝ)*X 1 1+(5443044069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276834303/10000000000 : ℝ)*X 2 0+(5443044039/10000000000 : ℝ)*X 2 1+(-1466084021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4174819987/10000000000 : ℝ)*X 0 0+(903969797/2000000000 : ℝ)*X 0 1+(769882603/2000000000 : ℝ)*X 0 2+(4174819987/10000000000 : ℝ)*X 1 0+(903969797/2000000000 : ℝ)*X 1 1+(769882603/2000000000 : ℝ)*X 1 2+(4174819987/10000000000 : ℝ)*X 2 0+(903969797/2000000000 : ℝ)*X 2 1+(769882603/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69298789533281511944049/6935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (785951913/50000000000000 : ℝ)*(base19) + (178865889/12500000000000 : ℝ)*(base23) + (59635043/100000000000000 : ℝ)*(lower2) + (244970907/100000000000000 : ℝ)*(upper3) + (166792403/100000000000000 : ℝ)*(upper5) + (1326848363961299/50000000000000 : ℝ)*(major0) + (1326848363961299/50000000000000 : ℝ)*(major1) + (1326848363961299/50000000000000 : ℝ)*(major2) + (1919271250279827/50000000000000 : ℝ)*(sp0) + (1919279972902051/50000000000000 : ℝ)*(sp1) + (767712017356163/20000000000000 : ℝ)*(sp2) + (293764695675001/20000000000000 : ℝ)*(sp3) + (9508574137/50000000000000 : ℝ)*(sp4) + (4063337533/50000000000000 : ℝ)*(sp7) + (1468831605050071/100000000000000 : ℝ)*(f.failure) + (479820189713491/12500000000000 : ℝ)*(f.sum) + (22577993146917/6935000000000000000000000000 : ℝ)*base65 + (350072528091769871/36500000000000000000000000000000 : ℝ)*base68 + (12951774971269871/36500000000000000000000000000000 : ℝ)*base70 + (126766603097230129/36500000000000000000000000000000 : ℝ)*base71 + (17129787034063/6935000000000000000000000000 : ℝ)*base74 + (274194937405269871/36500000000000000000000000000000 : ℝ)*base76 + (25240046967730129/36500000000000000000000000000000 : ℝ)*base77 + (86912084795730129/36500000000000000000000000000000 : ℝ)*base79 + (36386106496827/6935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (41664897/5000000000000000000000 : ℝ)*base90 + (41664897/5000000000000000000000 : ℝ)*base92 + (41664897/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1505285031104326387060586421/173375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284616189/50000000000000 : ℝ)*(base19) + (238508383/25000000000000 : ℝ)*(base23) + (215637153/100000000000000 : ℝ)*(lower1) + (49555303/50000000000000 : ℝ)*(upper3) + (105685293/50000000000000 : ℝ)*(lower4) + (205187137/100000000000000 : ℝ)*(upper5) + (673690629680057/25000000000000 : ℝ)*(major0) + (673690629680057/25000000000000 : ℝ)*(major1) + (673690629680057/25000000000000 : ℝ)*(major2) + (132403889/10000000000000 : ℝ)*(sp2) + (974490766453157/25000000000000 : ℝ)*(sp4) + (3897962496580251/100000000000000 : ℝ)*(sp5) + (1948980393870103/50000000000000 : ℝ)*(sp6) + (1491561682219497/100000000000000 : ℝ)*(sp7) + (1491561682219497/100000000000000 : ℝ)*(f.failure) + (974490766453157/25000000000000 : ℝ)*(f.sum) + (6466836596507/6935000000000000000000000000 : ℝ)*base65 + (46163860451596253/18250000000000000000000000000000 : ℝ)*base68 + (4547358666903747/18250000000000000000000000000000 : ℝ)*base69 + (415740220629903747/18250000000000000000000000000000 : ℝ)*base71 + (19928812764627/6935000000000000000000000000 : ℝ)*base73 + (576400715057846253/18250000000000000000000000000000 : ℝ)*base76 + (78192007139903747/18250000000000000000000000000000 : ℝ)*base77 + (8648234443403747/18250000000000000000000000000000 : ℝ)*base79 + (456191651693/6935000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (21337279/5000000000000000000000 : ℝ)*base90 + (21337279/5000000000000000000000 : ℝ)*base92 + (21337279/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1658_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (508/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2677/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1658_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1658_box_0 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-667695779/5000000000 : ℝ)*x 0 + (2703051847/5000000000 : ℝ)*x 1 + (5406104959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667695779/5000000000 : ℝ)^4951 ≤ (246861497943/3125000000000 : ℝ)^3927 := by
    have hnat : (667695779 : ℕ)^4951*3125000000000^3927 ≤ 246861497943^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667695779 5000000000 246861497943 3125000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703051847/5000000000 : ℝ)^4951 ≤ (23025104616919/50000000000000 : ℝ)^3927 := by
    have hnat : (2703051847 : ℕ)^4951*50000000000000^3927 ≤ 23025104616919^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703051847 5000000000 23025104616919 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406104959/10000000000 : ℝ)^4951 ≤ (11512555704789/25000000000000 : ℝ)^3927 := by
    have hnat : (5406104959 : ℕ)^4951*25000000000000^3927 ≤ 11512555704789^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406104959 10000000000 11512555704789 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-667695779/5000000000 : ℝ), (2703051847/5000000000 : ℝ), (5406104959/10000000000 : ℝ)] ![(246861497943/3125000000000 : ℝ), (23025104616919/50000000000000 : ℝ), (11512555704789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-667695779/5000000000 : ℝ)|^4951 ≤ (246861497943/3125000000000 : ℝ)^3927
        have hw : |(-667695779/5000000000 : ℝ)|=(667695779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703051847/5000000000 : ℝ)|^4951 ≤ (23025104616919/50000000000000 : ℝ)^3927
        have hw : |(2703051847/5000000000 : ℝ)|=(2703051847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406104959/10000000000 : ℝ)|^4951 ≤ (11512555704789/25000000000000 : ℝ)^3927
        have hw : |(5406104959/10000000000 : ℝ)|=(5406104959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_1 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312737439/2500000000 : ℝ)*x 0 + (-31069953/200000000 : ℝ)*x 1 + (216244163/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312737439/2500000000 : ℝ)^4951 ≤ (44390231490401/100000000000000 : ℝ)^3927 := by
    have hnat : (1312737439 : ℕ)^4951*100000000000000^3927 ≤ 44390231490401^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312737439 2500000000 44390231490401 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31069953/200000000 : ℝ)^4951 ≤ (597472197733/6250000000000 : ℝ)^3927 := by
    have hnat : (31069953 : ℕ)^4951*6250000000000^3927 ≤ 597472197733^3927*200000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31069953 200000000 597472197733 6250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216244163/400000000 : ℝ)^4951 ≤ (46050213325543/100000000000000 : ℝ)^3927 := by
    have hnat : (216244163 : ℕ)^4951*100000000000000^3927 ≤ 46050213325543^3927*400000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216244163 400000000 46050213325543 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312737439/2500000000 : ℝ), (-31069953/200000000 : ℝ), (216244163/400000000 : ℝ)] ![(44390231490401/100000000000000 : ℝ), (597472197733/6250000000000 : ℝ), (46050213325543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312737439/2500000000 : ℝ)|^4951 ≤ (44390231490401/100000000000000 : ℝ)^3927
        have hw : |(1312737439/2500000000 : ℝ)|=(1312737439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31069953/200000000 : ℝ)|^4951 ≤ (597472197733/6250000000000 : ℝ)^3927
        have hw : |(-31069953/200000000 : ℝ)|=(31069953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216244163/400000000 : ℝ)|^4951 ≤ (46050213325543/100000000000000 : ℝ)^3927
        have hw : |(216244163/400000000 : ℝ)|=(216244163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_2 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250949519/10000000000 : ℝ)*x 0 + (1351526179/2500000000 : ℝ)*x 1 + (-1553497089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250949519/10000000000 : ℝ)^4951 ≤ (44390228964421/100000000000000 : ℝ)^3927 := by
    have hnat : (5250949519 : ℕ)^4951*100000000000000^3927 ≤ 44390228964421^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250949519 10000000000 44390228964421 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351526179/2500000000 : ℝ)^4951 ≤ (23025110104743/50000000000000 : ℝ)^3927 := by
    have hnat : (1351526179 : ℕ)^4951*50000000000000^3927 ≤ 23025110104743^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351526179 2500000000 23025110104743 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1553497089/10000000000 : ℝ)^4951 ≤ (2389887702849/25000000000000 : ℝ)^3927 := by
    have hnat : (1553497089 : ℕ)^4951*25000000000000^3927 ≤ 2389887702849^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553497089 10000000000 2389887702849 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250949519/10000000000 : ℝ), (1351526179/2500000000 : ℝ), (-1553497089/10000000000 : ℝ)] ![(44390228964421/100000000000000 : ℝ), (23025110104743/50000000000000 : ℝ), (2389887702849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250949519/10000000000 : ℝ)|^4951 ≤ (44390228964421/100000000000000 : ℝ)^3927
        have hw : |(5250949519/10000000000 : ℝ)|=(5250949519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351526179/2500000000 : ℝ)|^4951 ≤ (23025110104743/50000000000000 : ℝ)^3927
        have hw : |(1351526179/2500000000 : ℝ)|=(1351526179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1553497089/10000000000 : ℝ)|^4951 ≤ (2389887702849/25000000000000 : ℝ)^3927
        have hw : |(-1553497089/10000000000 : ℝ)|=(1553497089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_3 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4450938983/10000000000 : ℝ)*x 0 + (2024202741/5000000000 : ℝ)*x 1 + (4048405889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4450938983/10000000000 : ℝ)^4951 ≤ (18019896800717/50000000000000 : ℝ)^3927 := by
    have hnat : (4450938983 : ℕ)^4951*50000000000000^3927 ≤ 18019896800717^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450938983 10000000000 18019896800717 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024202741/5000000000 : ℝ)^4951 ≤ (1998756322787/6250000000000 : ℝ)^3927 := by
    have hnat : (2024202741 : ℕ)^4951*6250000000000^3927 ≤ 1998756322787^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024202741 5000000000 1998756322787 6250000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4048405889/10000000000 : ℝ)^4951 ≤ (15990052609009/50000000000000 : ℝ)^3927 := by
    have hnat : (4048405889 : ℕ)^4951*50000000000000^3927 ≤ 15990052609009^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048405889 10000000000 15990052609009 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4450938983/10000000000 : ℝ), (2024202741/5000000000 : ℝ), (4048405889/10000000000 : ℝ)] ![(18019896800717/50000000000000 : ℝ), (1998756322787/6250000000000 : ℝ), (15990052609009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4450938983/10000000000 : ℝ)|^4951 ≤ (18019896800717/50000000000000 : ℝ)^3927
        have hw : |(4450938983/10000000000 : ℝ)|=(4450938983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2024202741/5000000000 : ℝ)|^4951 ≤ (1998756322787/6250000000000 : ℝ)^3927
        have hw : |(2024202741/5000000000 : ℝ)|=(2024202741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4048405889/10000000000 : ℝ)|^4951 ≤ (15990052609009/50000000000000 : ℝ)^3927
        have hw : |(4048405889/10000000000 : ℝ)|=(4048405889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_4 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92812883/500000000 : ℝ)*x 0 + (1303981423/2500000000 : ℝ)*x 1 + (1043185417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92812883/500000000 : ℝ)^4951 ≤ (11965454867309/100000000000000 : ℝ)^3927 := by
    have hnat : (92812883 : ℕ)^4951*100000000000000^3927 ≤ 11965454867309^3927*500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92812883 500000000 11965454867309 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303981423/2500000000 : ℝ)^4951 ≤ (22008632572839/50000000000000 : ℝ)^3927 := by
    have hnat : (1303981423 : ℕ)^4951*50000000000000^3927 ≤ 22008632572839^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303981423 2500000000 22008632572839 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043185417/2000000000 : ℝ)^4951 ≤ (22008639983293/50000000000000 : ℝ)^3927 := by
    have hnat : (1043185417 : ℕ)^4951*50000000000000^3927 ≤ 22008639983293^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043185417 2000000000 22008639983293 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92812883/500000000 : ℝ), (1303981423/2500000000 : ℝ), (1043185417/2000000000 : ℝ)] ![(11965454867309/100000000000000 : ℝ), (22008632572839/50000000000000 : ℝ), (22008639983293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92812883/500000000 : ℝ)|^4951 ≤ (11965454867309/100000000000000 : ℝ)^3927
        have hw : |(-92812883/500000000 : ℝ)|=(92812883/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303981423/2500000000 : ℝ)|^4951 ≤ (22008632572839/50000000000000 : ℝ)^3927
        have hw : |(1303981423/2500000000 : ℝ)|=(1303981423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043185417/2000000000 : ℝ)|^4951 ≤ (22008639983293/50000000000000 : ℝ)^3927
        have hw : |(1043185417/2000000000 : ℝ)|=(1043185417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_5 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336333983/625000000 : ℝ)*x 0 + (-327054303/2000000000 : ℝ)*x 1 + (5215926083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336333983/625000000 : ℝ)^4951 ≤ (22892230740571/50000000000000 : ℝ)^3927 := by
    have hnat : (336333983 : ℕ)^4951*50000000000000^3927 ≤ 22892230740571^3927*625000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336333983 625000000 22892230740571 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327054303/2000000000 : ℝ)^4951 ≤ (2549567301267/25000000000000 : ℝ)^3927 := by
    have hnat : (327054303 : ℕ)^4951*25000000000000^3927 ≤ 2549567301267^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327054303 2000000000 2549567301267 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215926083/10000000000 : ℝ)^4951 ≤ (22008634652873/50000000000000 : ℝ)^3927 := by
    have hnat : (5215926083 : ℕ)^4951*50000000000000^3927 ≤ 22008634652873^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215926083 10000000000 22008634652873 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336333983/625000000 : ℝ), (-327054303/2000000000 : ℝ), (5215926083/10000000000 : ℝ)] ![(22892230740571/50000000000000 : ℝ), (2549567301267/25000000000000 : ℝ), (22008634652873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336333983/625000000 : ℝ)|^4951 ≤ (22892230740571/50000000000000 : ℝ)^3927
        have hw : |(336333983/625000000 : ℝ)|=(336333983/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-327054303/2000000000 : ℝ)|^4951 ≤ (2549567301267/25000000000000 : ℝ)^3927
        have hw : |(-327054303/2000000000 : ℝ)|=(327054303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215926083/10000000000 : ℝ)|^4951 ≤ (22008634652873/50000000000000 : ℝ)^3927
        have hw : |(5215926083/10000000000 : ℝ)|=(5215926083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_6 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381343981/10000000000 : ℝ)*x 0 + (1303981653/2500000000 : ℝ)*x 1 + (-408817613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381343981/10000000000 : ℝ)^4951 ≤ (11446116048739/25000000000000 : ℝ)^3927 := by
    have hnat : (5381343981 : ℕ)^4951*25000000000000^3927 ≤ 11446116048739^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381343981 10000000000 11446116048739 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303981653/2500000000 : ℝ)^4951 ≤ (22008637467037/50000000000000 : ℝ)^3927 := by
    have hnat : (1303981653 : ℕ)^4951*50000000000000^3927 ≤ 22008637467037^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303981653 2500000000 22008637467037 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408817613/2500000000 : ℝ)^4951 ≤ (5099130423539/50000000000000 : ℝ)^3927 := by
    have hnat : (408817613 : ℕ)^4951*50000000000000^3927 ≤ 5099130423539^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408817613 2500000000 5099130423539 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381343981/10000000000 : ℝ), (1303981653/2500000000 : ℝ), (-408817613/2500000000 : ℝ)] ![(11446116048739/25000000000000 : ℝ), (22008637467037/50000000000000 : ℝ), (5099130423539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381343981/10000000000 : ℝ)|^4951 ≤ (11446116048739/25000000000000 : ℝ)^3927
        have hw : |(5381343981/10000000000 : ℝ)|=(5381343981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303981653/2500000000 : ℝ)|^4951 ≤ (22008637467037/50000000000000 : ℝ)^3927
        have hw : |(1303981653/2500000000 : ℝ)|=(1303981653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408817613/2500000000 : ℝ)|^4951 ≤ (5099130423539/50000000000000 : ℝ)^3927
        have hw : |(-408817613/2500000000 : ℝ)|=(408817613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_7 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (389173557/1000000000 : ℝ)*x 0 + (2163842237/5000000000 : ℝ)*x 1 + (216384347/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389173557/1000000000 : ℝ)^4951 ≤ (15213865516759/50000000000000 : ℝ)^3927 := by
    have hnat : (389173557 : ℕ)^4951*50000000000000^3927 ≤ 15213865516759^3927*1000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389173557 1000000000 15213865516759 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163842237/5000000000 : ℝ)^4951 ≤ (34786121983519/100000000000000 : ℝ)^3927 := by
    have hnat : (2163842237 : ℕ)^4951*100000000000000^3927 ≤ 34786121983519^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163842237 5000000000 34786121983519 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216384347/500000000 : ℝ)^4951 ≤ (6957229394811/20000000000000 : ℝ)^3927 := by
    have hnat : (216384347 : ℕ)^4951*20000000000000^3927 ≤ 6957229394811^3927*500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216384347 500000000 6957229394811 20000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(389173557/1000000000 : ℝ), (2163842237/5000000000 : ℝ), (216384347/500000000 : ℝ)] ![(15213865516759/50000000000000 : ℝ), (34786121983519/100000000000000 : ℝ), (6957229394811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(389173557/1000000000 : ℝ)|^4951 ≤ (15213865516759/50000000000000 : ℝ)^3927
        have hw : |(389173557/1000000000 : ℝ)|=(389173557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2163842237/5000000000 : ℝ)|^4951 ≤ (34786121983519/100000000000000 : ℝ)^3927
        have hw : |(2163842237/5000000000 : ℝ)|=(2163842237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216384347/500000000 : ℝ)|^4951 ≤ (6957229394811/20000000000000 : ℝ)^3927
        have hw : |(216384347/500000000 : ℝ)|=(216384347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_8 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1745090341/10000000000 : ℝ)*x 0 + (101579341/200000000 : ℝ)*x 1 + (54354617/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1745090341/10000000000 : ℝ)^4951 ≤ (5534587159561/50000000000000 : ℝ)^3927 := by
    have hnat : (1745090341 : ℕ)^4951*50000000000000^3927 ≤ 5534587159561^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745090341 10000000000 5534587159561 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101579341/200000000 : ℝ)^4951 ≤ (5320638333583/12500000000000 : ℝ)^3927 := by
    have hnat : (101579341 : ℕ)^4951*12500000000000^3927 ≤ 5320638333583^3927*200000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101579341 200000000 5320638333583 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54354617/100000000 : ℝ)^4951 ≤ (46365718988083/100000000000000 : ℝ)^3927 := by
    have hnat : (54354617 : ℕ)^4951*100000000000000^3927 ≤ 46365718988083^3927*100000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54354617 100000000 46365718988083 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1745090341/10000000000 : ℝ), (101579341/200000000 : ℝ), (54354617/100000000 : ℝ)] ![(5534587159561/50000000000000 : ℝ), (5320638333583/12500000000000 : ℝ), (46365718988083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1745090341/10000000000 : ℝ)|^4951 ≤ (5534587159561/50000000000000 : ℝ)^3927
        have hw : |(-1745090341/10000000000 : ℝ)|=(1745090341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(101579341/200000000 : ℝ)|^4951 ≤ (5320638333583/12500000000000 : ℝ)^3927
        have hw : |(101579341/200000000 : ℝ)|=(101579341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54354617/100000000 : ℝ)|^4951 ≤ (46365718988083/100000000000000 : ℝ)^3927
        have hw : |(54354617/100000000 : ℝ)|=(54354617/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_9 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046164611/2000000000 : ℝ)*x 0 + (-385113081/2500000000 : ℝ)*x 1 + (543546143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046164611/2000000000 : ℝ)^4951 ≤ (22087912760379/50000000000000 : ℝ)^3927 := by
    have hnat : (1046164611 : ℕ)^4951*50000000000000^3927 ≤ 22087912760379^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046164611 2000000000 22087912760379 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385113081/2500000000 : ℝ)^4951 ≤ (4729229193457/50000000000000 : ℝ)^3927 := by
    have hnat : (385113081 : ℕ)^4951*50000000000000^3927 ≤ 4729229193457^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385113081 2500000000 4729229193457 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543546143/1000000000 : ℝ)^4951 ≤ (46365716084353/100000000000000 : ℝ)^3927 := by
    have hnat : (543546143 : ℕ)^4951*100000000000000^3927 ≤ 46365716084353^3927*1000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543546143 1000000000 46365716084353 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046164611/2000000000 : ℝ), (-385113081/2500000000 : ℝ), (543546143/1000000000 : ℝ)] ![(22087912760379/50000000000000 : ℝ), (4729229193457/50000000000000 : ℝ), (46365716084353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046164611/2000000000 : ℝ)|^4951 ≤ (22087912760379/50000000000000 : ℝ)^3927
        have hw : |(1046164611/2000000000 : ℝ)|=(1046164611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385113081/2500000000 : ℝ)|^4951 ≤ (4729229193457/50000000000000 : ℝ)^3927
        have hw : |(-385113081/2500000000 : ℝ)|=(385113081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543546143/1000000000 : ℝ)|^4951 ≤ (46365716084353/100000000000000 : ℝ)^3927
        have hw : |(543546143/1000000000 : ℝ)|=(543546143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_10 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046164663/2000000000 : ℝ)*x 0 + (5435461491/10000000000 : ℝ)*x 1 + (-1540451881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046164663/2000000000 : ℝ)^4951 ≤ (22087914144551/50000000000000 : ℝ)^3927 := by
    have hnat : (1046164663 : ℕ)^4951*50000000000000^3927 ≤ 22087914144551^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046164663 2000000000 22087914144551 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435461491/10000000000 : ℝ)^4951 ≤ (46365716740381/100000000000000 : ℝ)^3927 := by
    have hnat : (5435461491 : ℕ)^4951*100000000000000^3927 ≤ 46365716740381^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435461491 10000000000 46365716740381 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1540451881/10000000000 : ℝ)^4951 ≤ (2364613739399/25000000000000 : ℝ)^3927 := by
    have hnat : (1540451881 : ℕ)^4951*25000000000000^3927 ≤ 2364613739399^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540451881 10000000000 2364613739399 25000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046164663/2000000000 : ℝ), (5435461491/10000000000 : ℝ), (-1540451881/10000000000 : ℝ)] ![(22087914144551/50000000000000 : ℝ), (46365716740381/100000000000000 : ℝ), (2364613739399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046164663/2000000000 : ℝ)|^4951 ≤ (22087914144551/50000000000000 : ℝ)^3927
        have hw : |(1046164663/2000000000 : ℝ)|=(1046164663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435461491/10000000000 : ℝ)|^4951 ≤ (46365716740381/100000000000000 : ℝ)^3927
        have hw : |(5435461491/10000000000 : ℝ)|=(5435461491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1540451881/10000000000 : ℝ)|^4951 ≤ (2364613739399/25000000000000 : ℝ)^3927
        have hw : |(-1540451881/10000000000 : ℝ)|=(1540451881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_11 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (906977183/2000000000 : ℝ)*x 0 + (4005216781/10000000000 : ℝ)*x 1 + (4005215733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (906977183/2000000000 : ℝ)^4951 ≤ (18449432465903/50000000000000 : ℝ)^3927 := by
    have hnat : (906977183 : ℕ)^4951*50000000000000^3927 ≤ 18449432465903^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906977183 2000000000 18449432465903 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4005216781/10000000000 : ℝ)^4951 ≤ (31550572730599/100000000000000 : ℝ)^3927 := by
    have hnat : (4005216781 : ℕ)^4951*100000000000000^3927 ≤ 31550572730599^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005216781 10000000000 31550572730599 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4005215733/10000000000 : ℝ)^4951 ≤ (15775281161213/50000000000000 : ℝ)^3927 := by
    have hnat : (4005215733 : ℕ)^4951*50000000000000^3927 ≤ 15775281161213^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005215733 10000000000 15775281161213 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(906977183/2000000000 : ℝ), (4005216781/10000000000 : ℝ), (4005215733/10000000000 : ℝ)] ![(18449432465903/50000000000000 : ℝ), (31550572730599/100000000000000 : ℝ), (15775281161213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(906977183/2000000000 : ℝ)|^4951 ≤ (18449432465903/50000000000000 : ℝ)^3927
        have hw : |(906977183/2000000000 : ℝ)|=(906977183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4005216781/10000000000 : ℝ)|^4951 ≤ (31550572730599/100000000000000 : ℝ)^3927
        have hw : |(4005216781/10000000000 : ℝ)|=(4005216781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4005215733/10000000000 : ℝ)|^4951 ≤ (15775281161213/50000000000000 : ℝ)^3927
        have hw : |(4005215733/10000000000 : ℝ)|=(4005215733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_12 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1444699063/10000000000 : ℝ)*x 0 + (346118021/625000000 : ℝ)*x 1 + (5196126207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1444699063/10000000000 : ℝ)^4951 ≤ (348932885653/4000000000000 : ℝ)^3927 := by
    have hnat : (1444699063 : ℕ)^4951*4000000000000^3927 ≤ 348932885653^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444699063 10000000000 348932885653 4000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346118021/625000000 : ℝ)^4951 ≤ (23734983079859/50000000000000 : ℝ)^3927 := by
    have hnat : (346118021 : ℕ)^4951*50000000000000^3927 ≤ 23734983079859^3927*625000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346118021 625000000 23734983079859 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196126207/10000000000 : ℝ)^4951 ≤ (43806711684377/100000000000000 : ℝ)^3927 := by
    have hnat : (5196126207 : ℕ)^4951*100000000000000^3927 ≤ 43806711684377^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196126207 10000000000 43806711684377 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1444699063/10000000000 : ℝ), (346118021/625000000 : ℝ), (5196126207/10000000000 : ℝ)] ![(348932885653/4000000000000 : ℝ), (23734983079859/50000000000000 : ℝ), (43806711684377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1444699063/10000000000 : ℝ)|^4951 ≤ (348932885653/4000000000000 : ℝ)^3927
        have hw : |(-1444699063/10000000000 : ℝ)|=(1444699063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346118021/625000000 : ℝ)|^4951 ≤ (23734983079859/50000000000000 : ℝ)^3927
        have hw : |(346118021/625000000 : ℝ)|=(346118021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196126207/10000000000 : ℝ)|^4951 ≤ (43806711684377/100000000000000 : ℝ)^3927
        have hw : |(5196126207/10000000000 : ℝ)|=(5196126207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_13 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348732743/2500000000 : ℝ)*x 0 + (-821752007/5000000000 : ℝ)*x 1 + (2598062821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348732743/2500000000 : ℝ)^4951 ≤ (45930253460073/100000000000000 : ℝ)^3927 := by
    have hnat : (1348732743 : ℕ)^4951*100000000000000^3927 ≤ 45930253460073^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348732743 2500000000 45930253460073 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (821752007/5000000000 : ℝ)^4951 ≤ (410521633991/4000000000000 : ℝ)^3927 := by
    have hnat : (821752007 : ℕ)^4951*4000000000000^3927 ≤ 410521633991^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821752007 5000000000 410521633991 4000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598062821/5000000000 : ℝ)^4951 ≤ (5475838209873/12500000000000 : ℝ)^3927 := by
    have hnat : (2598062821 : ℕ)^4951*12500000000000^3927 ≤ 5475838209873^3927*5000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598062821 5000000000 5475838209873 12500000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348732743/2500000000 : ℝ), (-821752007/5000000000 : ℝ), (2598062821/5000000000 : ℝ)] ![(45930253460073/100000000000000 : ℝ), (410521633991/4000000000000 : ℝ), (5475838209873/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348732743/2500000000 : ℝ)|^4951 ≤ (45930253460073/100000000000000 : ℝ)^3927
        have hw : |(1348732743/2500000000 : ℝ)|=(1348732743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-821752007/5000000000 : ℝ)|^4951 ≤ (410521633991/4000000000000 : ℝ)^3927
        have hw : |(-821752007/5000000000 : ℝ)|=(821752007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598062821/5000000000 : ℝ)|^4951 ≤ (5475838209873/12500000000000 : ℝ)^3927
        have hw : |(2598062821/5000000000 : ℝ)|=(2598062821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_14 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078986059/2000000000 : ℝ)*x 0 + (129903153/250000000 : ℝ)*x 1 + (-410876073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078986059/2000000000 : ℝ)^4951 ≤ (45930246193433/100000000000000 : ℝ)^3927 := by
    have hnat : (1078986059 : ℕ)^4951*100000000000000^3927 ≤ 45930246193433^3927*2000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078986059 2000000000 45930246193433 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129903153/250000000 : ℝ)^4951 ≤ (43806710759653/100000000000000 : ℝ)^3927 := by
    have hnat : (129903153 : ℕ)^4951*100000000000000^3927 ≤ 43806710759653^3927*250000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129903153 250000000 43806710759653 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410876073/2500000000 : ℝ)^4951 ≤ (5131521519227/50000000000000 : ℝ)^3927 := by
    have hnat : (410876073 : ℕ)^4951*50000000000000^3927 ≤ 5131521519227^3927*2500000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410876073 2500000000 5131521519227 50000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078986059/2000000000 : ℝ), (129903153/250000000 : ℝ), (-410876073/2500000000 : ℝ)] ![(45930246193433/100000000000000 : ℝ), (43806710759653/100000000000000 : ℝ), (5131521519227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078986059/2000000000 : ℝ)|^4951 ≤ (45930246193433/100000000000000 : ℝ)^3927
        have hw : |(1078986059/2000000000 : ℝ)|=(1078986059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129903153/250000000 : ℝ)|^4951 ≤ (43806710759653/100000000000000 : ℝ)^3927
        have hw : |(129903153/250000000 : ℝ)|=(129903153/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410876073/2500000000 : ℝ)|^4951 ≤ (5131521519227/50000000000000 : ℝ)^3927
        have hw : |(-410876073/2500000000 : ℝ)|=(410876073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1658_box_15 (p : ℝ) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (119746409/312500000 : ℝ)*x 0 + (4356709809/10000000000 : ℝ)*x 1 + (4356709901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119746409/312500000 : ℝ)^4951 ≤ (932467309979/3125000000000 : ℝ)^3927 := by
    have hnat : (119746409 : ℕ)^4951*3125000000000^3927 ≤ 932467309979^3927*312500000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119746409 312500000 932467309979 3125000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4356709809/10000000000 : ℝ)^4951 ≤ (35080522566729/100000000000000 : ℝ)^3927 := by
    have hnat : (4356709809 : ℕ)^4951*100000000000000^3927 ≤ 35080522566729^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356709809 10000000000 35080522566729 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4356709901/10000000000 : ℝ)^4951 ≤ (35080523500687/100000000000000 : ℝ)^3927 := by
    have hnat : (4356709901 : ℕ)^4951*100000000000000^3927 ≤ 35080523500687^3927*10000000000^4951 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356709901 10000000000 35080523500687 100000000000000 4951 3927 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4951/1024 : ℝ)) 4951 3927 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(119746409/312500000 : ℝ), (4356709809/10000000000 : ℝ), (4356709901/10000000000 : ℝ)] ![(932467309979/3125000000000 : ℝ), (35080522566729/100000000000000 : ℝ), (35080523500687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(119746409/312500000 : ℝ)|^4951 ≤ (932467309979/3125000000000 : ℝ)^3927
        have hw : |(119746409/312500000 : ℝ)|=(119746409/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4356709809/10000000000 : ℝ)|^4951 ≤ (35080522566729/100000000000000 : ℝ)^3927
        have hw : |(4356709809/10000000000 : ℝ)|=(4356709809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4356709901/10000000000 : ℝ)|^4951 ≤ (35080523500687/100000000000000 : ℝ)^3927
        have hw : |(4356709901/10000000000 : ℝ)|=(4356709901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1658_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(32551/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7339/12500 : ℝ) ∧ (81341/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88301/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4063/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4063/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4063/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4063/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4063/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4063/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10711/100000 : ℝ) ^ (4947/1024 : ℝ) ≤ (2056154606837707/100000000000000000000 : ℝ) := by
    have hpowers : (10711/100000 : ℝ)^4947 ≤ (2056154606837707/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10711 : ℕ)^4947*100000000000000000000^1024 ≤ 2056154606837707^1024*100000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10711 100000 2056154606837707 100000000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10711/100000 : ℝ)) (X := (2056154606837707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4063/25000 : ℝ) ^ (4947/1024 : ℝ) ≤ (481612427506651/3125000000000000000 : ℝ) := by
    have hpowers : (4063/25000 : ℝ)^4947 ≤ (481612427506651/3125000000000000000 : ℝ)^1024 := by
      have hnat : (4063 : ℕ)^4947*3125000000000000000^1024 ≤ 481612427506651^1024*25000^4947 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4063 25000 481612427506651 3125000000000000000 4947 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4063/25000 : ℝ)) (X := (481612427506651/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002056154606837707/50000000000000000000 : ℝ) ≤ (2500021280250527/2500000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (50002056154606837707/50000000000000000000 : ℝ)^1024 ≤ (2500021280250527/2500000000000000 : ℝ)^4947 := by
      have hnat : (50002056154606837707 : ℕ)^1024*2500000000000000^4947 ≤ 2500021280250527^4947*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002056154606837707 50000000000000000000 2500021280250527 2500000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500021280250527/2500000000000000 : ℝ)) (X := (50002056154606837707/50000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017467752287050539/100000000000000000000 : ℝ) ≤ (10000361547192571/10000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (100017467752287050539/100000000000000000000 : ℝ)^1024 ≤ (10000361547192571/10000000000000000 : ℝ)^4947 := by
      have hnat : (100017467752287050539 : ℕ)^1024*10000000000000000^4947 ≤ 10000361547192571^4947*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017467752287050539 100000000000000000000 10000361547192571 10000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000361547192571/10000000000000000 : ℝ)) (X := (100017467752287050539/100000000000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1562981612427506651/1562500000000000000 : ℝ) ≤ (5000318986691517/5000000000000000 : ℝ) ^ (4947/1024 : ℝ) := by
    have hpowers : (1562981612427506651/1562500000000000000 : ℝ)^1024 ≤ (5000318986691517/5000000000000000 : ℝ)^4947 := by
      have hnat : (1562981612427506651 : ℕ)^1024*5000000000000000^4947 ≤ 5000318986691517^4947*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562981612427506651 1562500000000000000 5000318986691517 5000000000000000 1024 4947 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000318986691517/5000000000000000 : ℝ)) (X := (1562981612427506651/1562500000000000000 : ℝ)) (by norm_num) 4947 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2056154606837707/100000000000000000000 : ℝ) ≤ ((27702275026810291021/27705000000000000000 : ℝ)+2*(276426190463/554100000000000 : ℝ)*(10711/100000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (27702275026810291021/27705000000000000000 : ℝ)+2*(276426190463/554100000000000 : ℝ)*(10711/100000 : ℝ)=(2500021280250527/2500000000000000 : ℝ) by norm_num, show 1+2*(2056154606837707/100000000000000000000 : ℝ)=(50002056154606837707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(481612427506651/3125000000000000000 : ℝ)+(2056154606837707/100000000000000000000 : ℝ) ≤ ((27702275026810291021/27705000000000000000 : ℝ)+(276426190463/554100000000000 : ℝ)*((4063/25000 : ℝ)+(10711/100000 : ℝ)))^(4947/1024 : ℝ) := by
    rw [show (27702275026810291021/27705000000000000000 : ℝ)+(276426190463/554100000000000 : ℝ)*((4063/25000 : ℝ)+(10711/100000 : ℝ))=(10000361547192571/10000000000000000 : ℝ) by norm_num, show 1+(481612427506651/3125000000000000000 : ℝ)+(2056154606837707/100000000000000000000 : ℝ)=(100017467752287050539/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(481612427506651/3125000000000000000 : ℝ) ≤ ((27702275026810291021/27705000000000000000 : ℝ)+2*(276426190463/554100000000000 : ℝ)*(4063/25000 : ℝ))^(4947/1024 : ℝ) := by
    rw [show (27702275026810291021/27705000000000000000 : ℝ)+2*(276426190463/554100000000000 : ℝ)*(4063/25000 : ℝ)=(5000318986691517/5000000000000000 : ℝ) by norm_num, show 1+2*(481612427506651/3125000000000000000 : ℝ)=(1562981612427506651/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27702275026810291021/27705000000000000000 : ℝ)*(X 1 0+X 2 0)+(276426190463/554100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (27702275026810291021/27705000000000000000 : ℝ)) (alpha := (276426190463/554100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27702275026810291021/27705000000000000000 : ℝ)*(X 0 1+X 2 1)+(276426190463/554100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (27702275026810291021/27705000000000000000 : ℝ)) (alpha := (276426190463/554100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27702275026810291021/27705000000000000000 : ℝ)*(X 0 2+X 1 2)+(276426190463/554100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4947/1024 : ℝ)) (lo := (10711/100000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (27702275026810291021/27705000000000000000 : ℝ)) (alpha := (276426190463/554100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-667695779/5000000000 : ℝ)*X 0 0+(2703051847/5000000000 : ℝ)*X 0 1+(5406104959/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1312737439/2500000000 : ℝ)*X 1 0+(-31069953/200000000 : ℝ)*X 1 1+(216244163/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250949519/10000000000 : ℝ)*X 2 0+(1351526179/2500000000 : ℝ)*X 2 1+(-1553497089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4450938983/10000000000 : ℝ)*X 0 0+(2024202741/5000000000 : ℝ)*X 0 1+(4048405889/10000000000 : ℝ)*X 0 2+(4450938983/10000000000 : ℝ)*X 1 0+(2024202741/5000000000 : ℝ)*X 1 1+(4048405889/10000000000 : ℝ)*X 1 2+(4450938983/10000000000 : ℝ)*X 2 0+(2024202741/5000000000 : ℝ)*X 2 1+(4048405889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92812883/500000000 : ℝ)*X 0 0+(1303981423/2500000000 : ℝ)*X 0 1+(1043185417/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((336333983/625000000 : ℝ)*X 1 0+(-327054303/2000000000 : ℝ)*X 1 1+(5215926083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381343981/10000000000 : ℝ)*X 2 0+(1303981653/2500000000 : ℝ)*X 2 1+(-408817613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((389173557/1000000000 : ℝ)*X 0 0+(2163842237/5000000000 : ℝ)*X 0 1+(216384347/500000000 : ℝ)*X 0 2+(389173557/1000000000 : ℝ)*X 1 0+(2163842237/5000000000 : ℝ)*X 1 1+(216384347/500000000 : ℝ)*X 1 2+(389173557/1000000000 : ℝ)*X 2 0+(2163842237/5000000000 : ℝ)*X 2 1+(216384347/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1745090341/10000000000 : ℝ)*X 0 0+(101579341/200000000 : ℝ)*X 0 1+(54354617/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046164611/2000000000 : ℝ)*X 1 0+(-385113081/2500000000 : ℝ)*X 1 1+(543546143/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1046164663/2000000000 : ℝ)*X 2 0+(5435461491/10000000000 : ℝ)*X 2 1+(-1540451881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((906977183/2000000000 : ℝ)*X 0 0+(4005216781/10000000000 : ℝ)*X 0 1+(4005215733/10000000000 : ℝ)*X 0 2+(906977183/2000000000 : ℝ)*X 1 0+(4005216781/10000000000 : ℝ)*X 1 1+(4005215733/10000000000 : ℝ)*X 1 2+(906977183/2000000000 : ℝ)*X 2 0+(4005216781/10000000000 : ℝ)*X 2 1+(4005215733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1444699063/10000000000 : ℝ)*X 0 0+(346118021/625000000 : ℝ)*X 0 1+(5196126207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348732743/2500000000 : ℝ)*X 1 0+(-821752007/5000000000 : ℝ)*X 1 1+(2598062821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1078986059/2000000000 : ℝ)*X 2 0+(129903153/250000000 : ℝ)*X 2 1+(-410876073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((119746409/312500000 : ℝ)*X 0 0+(4356709809/10000000000 : ℝ)*X 0 1+(4356709901/10000000000 : ℝ)*X 0 2+(119746409/312500000 : ℝ)*X 1 0+(4356709809/10000000000 : ℝ)*X 1 1+(4356709901/10000000000 : ℝ)*X 1 2+(119746409/312500000 : ℝ)*X 2 0+(4356709809/10000000000 : ℝ)*X 2 1+(4356709901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1658_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32551/50000 : ℝ) ≤ (-150297582451852428315321017052851/230875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1770697/25000000000000 : ℝ)*(upper0) + (14659587/25000000000000 : ℝ)*(lower2) + (15268363/50000000000000 : ℝ)*(lower3) + (483923827/100000000000000 : ℝ)*(upper5) + (1774124505675539/100000000000000 : ℝ)*(major0) + (1774124505675539/100000000000000 : ℝ)*(major1) + (88706225283777/5000000000000 : ℝ)*(major2) + (3007409593/25000000000000 : ℝ)*(sp1) + (12553935673/100000000000000 : ℝ)*(sp2) + (350074379/5000000000000 : ℝ)*(sp3) + (1293981902718213/50000000000000 : ℝ)*(sp4) + (517590355159611/20000000000000 : ℝ)*(sp5) + (1293975625750377/50000000000000 : ℝ)*(sp6) + (490988954763747/50000000000000 : ℝ)*(sp7) + (39279396440603/4000000000000 : ℝ)*(f.failure) + (1293981902718213/50000000000000 : ℝ)*(f.sum) + (128180534760023/55410000000000000000000000000 : ℝ)*base66 + (4578554030871964681/2770500000000000000000000000000000 : ℝ)*base68 + (1145606144196708817/138525000000000000000000000000000 : ℝ)*base69 + (12456970811793964681/2770500000000000000000000000000000 : ℝ)*base72 + (270685965892267/55410000000000000000000000000 : ℝ)*base73 + (835069629472833817/138525000000000000000000000000000 : ℝ)*base75 + (22889719183191614681/2770500000000000000000000000000000 : ℝ)*base78 + (5275421403137114681/2770500000000000000000000000000000 : ℝ)*base80 + (7824723757841/13852500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2076579/200000000000000000000 : ℝ)*base89 + (2076579/200000000000000000000 : ℝ)*base91 + (76579/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (7339/12500 : ℝ) ≤ (67778406397444645286312026737387/115437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18008987/100000000000000 : ℝ)*(lower1) + (102520341/100000000000000 : ℝ)*(lower3) + (50992727/100000000000000 : ℝ)*(upper4) + (466414730227149/25000000000000 : ℝ)*(major0) + (466414730227149/25000000000000 : ℝ)*(major1) + (466414730227149/25000000000000 : ℝ)*(major2) + (669772307515461/25000000000000 : ℝ)*(sp0) + (267909644996197/10000000000000 : ℝ)*(sp1) + (334885958735991/12500000000000 : ℝ)*(sp2) + (129080735148767/12500000000000 : ℝ)*(sp3) + (362734997/100000000000000 : ℝ)*(sp5) + (4571404519/50000000000000 : ℝ)*(sp6) + (3689666963/100000000000000 : ℝ)*(sp7) + (3791317561/50000000000000 : ℝ)*(sp12) + (516324785428549/50000000000000 : ℝ)*(f.failure) + (1339548406348483/50000000000000 : ℝ)*(f.sum) + (14242622131821/2308750000000000000000000000 : ℝ)*base66 + (1902969568517756957/230875000000000000000000000000000 : ℝ)*base68 + (1556877330655756957/230875000000000000000000000000000 : ℝ)*base70 + (4263603412795756957/230875000000000000000000000000000 : ℝ)*base72 + (3424435666549/9235000000000000000000000000 : ℝ)*base74 + (3730179398255381957/230875000000000000000000000000000 : ℝ)*base76 + (1672349862243006957/230875000000000000000000000000000 : ℝ)*base78 + (1793534582101756957/230875000000000000000000000000000 : ℝ)*base80 + (3798944734959/577187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (24053443/2500000000000000000000 : ℝ)*base90 + (24053443/2500000000000000000000 : ℝ)*base92 + (24053443/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (81341/100000 : ℝ) ≤ (15024120485047258006692030115831/18470000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (940603/20000000000000 : ℝ)*(upper1) + (9824701/100000000000000 : ℝ)*(lower3) + (35015797/20000000000000 : ℝ)*(upper4) + (60639471/100000000000000 : ℝ)*(lower5) + (489495084258681/25000000000000 : ℝ)*(major0) + (489495084258681/25000000000000 : ℝ)*(major1) + (78319213481389/4000000000000 : ℝ)*(major2) + (5075297857/10000000000000 : ℝ)*(sp2) + (749900609/6250000000000 : ℝ)*(sp3) + (1394082797/50000000000000 : ℝ)*(sp4) + (1402546795178361/50000000000000 : ℝ)*(sp8) + (701274094630579/25000000000000 : ℝ)*(sp9) + (1402522812771873/50000000000000 : ℝ)*(sp10) + (216747568077523/20000000000000 : ℝ)*(sp11) + (1083749838797359/100000000000000 : ℝ)*(f.failure) + (701274094630579/25000000000000 : ℝ)*(f.sum) + (149528578997537/55410000000000000000000000000 : ℝ)*base65 + (402732985450165801/692625000000000000000000000000000 : ℝ)*base67 + (368446753938912169/110820000000000000000000000000000 : ℝ)*base69 + (3856955408971915801/692625000000000000000000000000000 : ℝ)*base71 + (27966313011103/55410000000000000000000000000 : ℝ)*base74 + (586317656027112169/110820000000000000000000000000000 : ℝ)*base75 + (729480418137957233/230875000000000000000000000000000 : ℝ)*base78 + (227942905625957233/230875000000000000000000000000000 : ℝ)*base80 + (99335755242521/9235000000000000000000000000 : ℝ)*base82 + (37380887/5000000000000000000000 : ℝ)*base89 + (37380887/5000000000000000000000 : ℝ)*base91 + (12619113/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88301/100000 : ℝ) ≤ (-407716960986240552299209086799701/461750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134035613/100000000000000 : ℝ)*(upper3) + (32801637/25000000000000 : ℝ)*(lower4) + (699973/3125000000000 : ℝ)*(upper5) + (50062190315323/2500000000000 : ℝ)*(major0) + (50062190315323/2500000000000 : ℝ)*(major1) + (2002487612612921/100000000000000 : ℝ)*(major2) + (6926505977/100000000000000 : ℝ)*(sp4) + (158113151069/100000000000000 : ℝ)*(sp5) + (54447061723/50000000000000 : ℝ)*(sp6) + (62273117111/100000000000000 : ℝ)*(sp7) + (2926016242310451/100000000000000 : ℝ)*(sp12) + (2925865055665359/100000000000000 : ℝ)*(sp13) + (1462957137346491/50000000000000 : ℝ)*(sp14) + (138540314781111/12500000000000 : ℝ)*(sp15) + (554192395682999/50000000000000 : ℝ)*(f.failure) + (731505792204107/25000000000000 : ℝ)*(f.sum) + (10982071978391/18470000000000000000000000000 : ℝ)*base65 + (370585308406560489/23087500000000000000000000000000 : ℝ)*base68 + (1628757236272627447/923500000000000000000000000000000 : ℝ)*base69 + (54215609780260489/23087500000000000000000000000000 : ℝ)*base72 + (148401971987689/18470000000000000000000000000 : ℝ)*base74 + (2674443856202127447/923500000000000000000000000000000 : ℝ)*base75 + (440217183122310217/69262500000000000000000000000000 : ℝ)*base78 + (671991891545910217/69262500000000000000000000000000 : ℝ)*base80 + (1558875556369/277050000000000000000000000 : ℝ)*base82 + (11314593/2500000000000000000000 : ℝ)*base90 + (11314593/2500000000000000000000 : ℝ)*base92 + (36314593/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1658_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32551/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7339/12500 : ℝ) else (81341/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88301/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1658_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1658_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32551/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7339/12500 : ℝ) else (81341/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88301/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1658_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1658_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1658_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4947/1024 : ℝ) ≤ p) (hpb : p ≤ (4951/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90333593/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (102/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32551/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(7339/12500 : ℝ) else (81341/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88301/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1658_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
