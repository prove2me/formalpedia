-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1608_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:58.444107+00:00
-- url     : https://prove2.me/submissions/58773027-9fa5-4cc0-8479-a25c12f07c0a

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
theorem support_rectangle_w1608_s0_0 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1569306863/10000000000 : ℝ)*x 0 + (5839835441/10000000000 : ℝ)*x 1 + (2445755021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1569306863/10000000000 : ℝ)^4751 ≤ (1886935918173/20000000000000 : ℝ)^3727 := by
    have hnat : (1569306863 : ℕ)^4751*20000000000000^3727 ≤ 1886935918173^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569306863 10000000000 1886935918173 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5839835441/10000000000 : ℝ)^4751 ≤ (157423214231/312500000000 : ℝ)^3727 := by
    have hnat : (5839835441 : ℕ)^4751*312500000000^3727 ≤ 157423214231^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5839835441 10000000000 157423214231 312500000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445755021/5000000000 : ℝ)^4751 ≤ (40189891834717/100000000000000 : ℝ)^3727 := by
    have hnat : (2445755021 : ℕ)^4751*100000000000000^3727 ≤ 40189891834717^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445755021 5000000000 40189891834717 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1569306863/10000000000 : ℝ), (5839835441/10000000000 : ℝ), (2445755021/5000000000 : ℝ)] ![(1886935918173/20000000000000 : ℝ), (157423214231/312500000000 : ℝ), (40189891834717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1569306863/10000000000 : ℝ)|^4751 ≤ (1886935918173/20000000000000 : ℝ)^3727
        have hw : |(-1569306863/10000000000 : ℝ)|=(1569306863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5839835441/10000000000 : ℝ)|^4751 ≤ (157423214231/312500000000 : ℝ)^3727
        have hw : |(5839835441/10000000000 : ℝ)|=(5839835441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2445755021/5000000000 : ℝ)|^4751 ≤ (40189891834717/100000000000000 : ℝ)^3727
        have hw : |(2445755021/5000000000 : ℝ)|=(2445755021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_1 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272727149/500000000 : ℝ)*x 0 + (-418920311/2000000000 : ℝ)*x 1 + (611438727/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272727149/500000000 : ℝ)^4751 ≤ (5772211903853/12500000000000 : ℝ)^3727 := by
    have hnat : (272727149 : ℕ)^4751*12500000000000^3727 ≤ 5772211903853^3727*500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272727149 500000000 5772211903853 12500000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (418920311/2000000000 : ℝ)^4751 ≤ (6816207643759/50000000000000 : ℝ)^3727 := by
    have hnat : (418920311 : ℕ)^4751*50000000000000^3727 ≤ 6816207643759^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418920311 2000000000 6816207643759 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611438727/1250000000 : ℝ)^4751 ≤ (2511868091729/6250000000000 : ℝ)^3727 := by
    have hnat : (611438727 : ℕ)^4751*6250000000000^3727 ≤ 2511868091729^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611438727 1250000000 2511868091729 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272727149/500000000 : ℝ), (-418920311/2000000000 : ℝ), (611438727/1250000000 : ℝ)] ![(5772211903853/12500000000000 : ℝ), (6816207643759/50000000000000 : ℝ), (2511868091729/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272727149/500000000 : ℝ)|^4751 ≤ (5772211903853/12500000000000 : ℝ)^3727
        have hw : |(272727149/500000000 : ℝ)|=(272727149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-418920311/2000000000 : ℝ)|^4751 ≤ (6816207643759/50000000000000 : ℝ)^3727
        have hw : |(-418920311/2000000000 : ℝ)|=(418920311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(611438727/1250000000 : ℝ)|^4751 ≤ (2511868091729/6250000000000 : ℝ)^3727
        have hw : |(611438727/1250000000 : ℝ)|=(611438727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_2 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218181713/400000000 : ℝ)*x 0 + (611438737/1250000000 : ℝ)*x 1 + (-418920331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218181713/400000000 : ℝ)^4751 ≤ (46177693558073/100000000000000 : ℝ)^3727 := by
    have hnat : (218181713 : ℕ)^4751*100000000000000^3727 ≤ 46177693558073^3727*400000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218181713 400000000 46177693558073 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611438737/1250000000 : ℝ)^4751 ≤ (40189890305559/100000000000000 : ℝ)^3727 := by
    have hnat : (611438737 : ℕ)^4751*100000000000000^3727 ≤ 40189890305559^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611438737 1250000000 40189890305559 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418920331/2000000000 : ℝ)^4751 ≤ (3408104029293/25000000000000 : ℝ)^3727 := by
    have hnat : (418920331 : ℕ)^4751*25000000000000^3727 ≤ 3408104029293^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418920331 2000000000 3408104029293 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218181713/400000000 : ℝ), (611438737/1250000000 : ℝ), (-418920331/2000000000 : ℝ)] ![(46177693558073/100000000000000 : ℝ), (40189890305559/100000000000000 : ℝ), (3408104029293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218181713/400000000 : ℝ)|^4751 ≤ (46177693558073/100000000000000 : ℝ)^3727
        have hw : |(218181713/400000000 : ℝ)|=(218181713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(611438737/1250000000 : ℝ)|^4751 ≤ (40189890305559/100000000000000 : ℝ)^3727
        have hw : |(611438737/1250000000 : ℝ)|=(611438737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418920331/2000000000 : ℝ)|^4751 ≤ (3408104029293/25000000000000 : ℝ)^3727
        have hw : |(-418920331/2000000000 : ℝ)|=(418920331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_3 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205538143/500000000 : ℝ)*x 0 + (96061519/312500000 : ℝ)*x 1 + (337387071/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205538143/500000000 : ℝ)^4751 ≤ (32199335624031/100000000000000 : ℝ)^3727 := by
    have hnat : (205538143 : ℕ)^4751*100000000000000^3727 ≤ 32199335624031^3727*500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205538143 500000000 32199335624031 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96061519/312500000 : ℝ)^4751 ≤ (11115114029099/50000000000000 : ℝ)^3727 := by
    have hnat : (96061519 : ℕ)^4751*50000000000000^3727 ≤ 11115114029099^3727*312500000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96061519 312500000 11115114029099 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337387071/625000000 : ℝ)^4751 ≤ (45570436312231/100000000000000 : ℝ)^3727 := by
    have hnat : (337387071 : ℕ)^4751*100000000000000^3727 ≤ 45570436312231^3727*625000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337387071 625000000 45570436312231 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205538143/500000000 : ℝ), (96061519/312500000 : ℝ), (337387071/625000000 : ℝ)] ![(32199335624031/100000000000000 : ℝ), (11115114029099/50000000000000 : ℝ), (45570436312231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205538143/500000000 : ℝ)|^4751 ≤ (32199335624031/100000000000000 : ℝ)^3727
        have hw : |(205538143/500000000 : ℝ)|=(205538143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96061519/312500000 : ℝ)|^4751 ≤ (11115114029099/50000000000000 : ℝ)^3727
        have hw : |(96061519/312500000 : ℝ)|=(96061519/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337387071/625000000 : ℝ)|^4751 ≤ (45570436312231/100000000000000 : ℝ)^3727
        have hw : |(337387071/625000000 : ℝ)|=(337387071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_4 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-314425461/2000000000 : ℝ)*x 0 + (2457768237/5000000000 : ℝ)*x 1 + (18171733/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (314425461/2000000000 : ℝ)^4751 ≤ (9456300266429/100000000000000 : ℝ)^3727 := by
    have hnat : (314425461 : ℕ)^4751*100000000000000^3727 ≤ 9456300266429^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314425461 2000000000 9456300266429 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2457768237/5000000000 : ℝ)^4751 ≤ (40441706727161/100000000000000 : ℝ)^3727 := by
    have hnat : (2457768237 : ℕ)^4751*100000000000000^3727 ≤ 40441706727161^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457768237 5000000000 40441706727161 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18171733/31250000 : ℝ)^4751 ≤ (3131374561533/6250000000000 : ℝ)^3727 := by
    have hnat : (18171733 : ℕ)^4751*6250000000000^3727 ≤ 3131374561533^3727*31250000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18171733 31250000 3131374561533 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-314425461/2000000000 : ℝ), (2457768237/5000000000 : ℝ), (18171733/31250000 : ℝ)] ![(9456300266429/100000000000000 : ℝ), (40441706727161/100000000000000 : ℝ), (3131374561533/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-314425461/2000000000 : ℝ)|^4751 ≤ (9456300266429/100000000000000 : ℝ)^3727
        have hw : |(-314425461/2000000000 : ℝ)|=(314425461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2457768237/5000000000 : ℝ)|^4751 ≤ (40441706727161/100000000000000 : ℝ)^3727
        have hw : |(2457768237/5000000000 : ℝ)|=(2457768237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18171733/31250000 : ℝ)|^4751 ≤ (3131374561533/6250000000000 : ℝ)^3727
        have hw : |(18171733/31250000 : ℝ)|=(18171733/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_5 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195537553/10000000000 : ℝ)*x 0 + (-585578257/5000000000 : ℝ)*x 1 + (5814954617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195537553/10000000000 : ℝ)^4751 ≤ (43400971384119/100000000000000 : ℝ)^3727 := by
    have hnat : (5195537553 : ℕ)^4751*100000000000000^3727 ≤ 43400971384119^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195537553 10000000000 43400971384119 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585578257/5000000000 : ℝ)^4751 ≤ (6497034991271/100000000000000 : ℝ)^3727 := by
    have hnat : (585578257 : ℕ)^4751*100000000000000^3727 ≤ 6497034991271^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585578257 5000000000 6497034991271 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5814954617/10000000000 : ℝ)^4751 ≤ (25050996805289/50000000000000 : ℝ)^3727 := by
    have hnat : (5814954617 : ℕ)^4751*50000000000000^3727 ≤ 25050996805289^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5814954617 10000000000 25050996805289 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195537553/10000000000 : ℝ), (-585578257/5000000000 : ℝ), (5814954617/10000000000 : ℝ)] ![(43400971384119/100000000000000 : ℝ), (6497034991271/100000000000000 : ℝ), (25050996805289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195537553/10000000000 : ℝ)|^4751 ≤ (43400971384119/100000000000000 : ℝ)^3727
        have hw : |(5195537553/10000000000 : ℝ)|=(5195537553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-585578257/5000000000 : ℝ)|^4751 ≤ (6497034991271/100000000000000 : ℝ)^3727
        have hw : |(-585578257/5000000000 : ℝ)|=(585578257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5814954617/10000000000 : ℝ)|^4751 ≤ (25050996805289/50000000000000 : ℝ)^3727
        have hw : |(5814954617/10000000000 : ℝ)|=(5814954617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_6 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195537623/10000000000 : ℝ)*x 0 + (1162990869/2000000000 : ℝ)*x 1 + (-1171156831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195537623/10000000000 : ℝ)^4751 ≤ (1736038885181/4000000000000 : ℝ)^3727 := by
    have hnat : (5195537623 : ℕ)^4751*4000000000000^3727 ≤ 1736038885181^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195537623 10000000000 1736038885181 4000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1162990869/2000000000 : ℝ)^4751 ≤ (5010199062311/10000000000000 : ℝ)^3727 := by
    have hnat : (1162990869 : ℕ)^4751*10000000000000^3727 ≤ 5010199062311^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162990869 2000000000 5010199062311 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171156831/10000000000 : ℝ)^4751 ≤ (649703723301/10000000000000 : ℝ)^3727 := by
    have hnat : (1171156831 : ℕ)^4751*10000000000000^3727 ≤ 649703723301^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171156831 10000000000 649703723301 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195537623/10000000000 : ℝ), (1162990869/2000000000 : ℝ), (-1171156831/10000000000 : ℝ)] ![(1736038885181/4000000000000 : ℝ), (5010199062311/10000000000000 : ℝ), (649703723301/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195537623/10000000000 : ℝ)|^4751 ≤ (1736038885181/4000000000000 : ℝ)^3727
        have hw : |(5195537623/10000000000 : ℝ)|=(5195537623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1162990869/2000000000 : ℝ)|^4751 ≤ (5010199062311/10000000000000 : ℝ)^3727
        have hw : |(1162990869/2000000000 : ℝ)|=(1162990869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1171156831/10000000000 : ℝ)|^4751 ≤ (649703723301/10000000000000 : ℝ)^3727
        have hw : |(-1171156831/10000000000 : ℝ)|=(1171156831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s0_7 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (823535353/2000000000 : ℝ)*x 0 + (1334826687/2500000000 : ℝ)*x 1 + (3134948867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823535353/2000000000 : ℝ)^4751 ≤ (1290735489463/4000000000000 : ℝ)^3727 := by
    have hnat : (823535353 : ℕ)^4751*4000000000000^3727 ≤ 1290735489463^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823535353 2000000000 1290735489463 4000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1334826687/2500000000 : ℝ)^4751 ≤ (22468850344509/50000000000000 : ℝ)^3727 := by
    have hnat : (1334826687 : ℕ)^4751*50000000000000^3727 ≤ 22468850344509^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334826687 2500000000 22468850344509 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134948867/10000000000 : ℝ)^4751 ≤ (22793912067307/100000000000000 : ℝ)^3727 := by
    have hnat : (3134948867 : ℕ)^4751*100000000000000^3727 ≤ 22793912067307^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134948867 10000000000 22793912067307 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(823535353/2000000000 : ℝ), (1334826687/2500000000 : ℝ), (3134948867/10000000000 : ℝ)] ![(1290735489463/4000000000000 : ℝ), (22468850344509/50000000000000 : ℝ), (22793912067307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(823535353/2000000000 : ℝ)|^4751 ≤ (1290735489463/4000000000000 : ℝ)^3727
        have hw : |(823535353/2000000000 : ℝ)|=(823535353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1334826687/2500000000 : ℝ)|^4751 ≤ (22468850344509/50000000000000 : ℝ)^3727
        have hw : |(1334826687/2500000000 : ℝ)|=(1334826687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134948867/10000000000 : ℝ)|^4751 ≤ (22793912067307/100000000000000 : ℝ)^3727
        have hw : |(3134948867/10000000000 : ℝ)|=(3134948867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1608_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3979/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (759/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4747/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4747 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4747*1^1024 ≤ 0^1024*1^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4747/1024 : ℝ) ≤ (1787157083061289/125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4747 ≤ (1787157083061289/125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4747*125000000000000000^1024 ≤ 1787157083061289^1024*5^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1787157083061289 125000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1787157083061289/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4747 := by
      have hnat : (1 : ℕ)^1024*1^4747 ≤ 1^4747*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (126787157083061289/125000000000000000 : ℝ) ≤ (1253833737017263/1250000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (126787157083061289/125000000000000000 : ℝ)^1024 ≤ (1253833737017263/1250000000000000 : ℝ)^4747 := by
      have hnat : (126787157083061289 : ℕ)^1024*1250000000000000^4747 ≤ 1253833737017263^4747*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126787157083061289 125000000000000000 1253833737017263 1250000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253833737017263/1250000000000000 : ℝ)) (X := (126787157083061289/125000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (64287157083061289/62500000000000000 : ℝ) ≤ (628833737017263/625000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (64287157083061289/62500000000000000 : ℝ)^1024 ≤ (628833737017263/625000000000000 : ℝ)^4747 := by
      have hnat : (64287157083061289 : ℕ)^1024*625000000000000^4747 ≤ 628833737017263^4747*62500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64287157083061289 62500000000000000 628833737017263 625000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628833737017263/625000000000000 : ℝ)) (X := (64287157083061289/62500000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3833737017263/500000000000000 : ℝ)*(0 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3833737017263/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1787157083061289/125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3833737017263/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4747/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3833737017263/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1253833737017263/1250000000000000 : ℝ) by norm_num, show 1+(1787157083061289/125000000000000000 : ℝ)+(0 : ℝ)=(126787157083061289/125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1787157083061289/125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3833737017263/500000000000000 : ℝ)*(2/5 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3833737017263/500000000000000 : ℝ)*(2/5 : ℝ)=(628833737017263/625000000000000 : ℝ) by norm_num, show 1+2*(1787157083061289/125000000000000000 : ℝ)=(64287157083061289/62500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3833737017263/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3833737017263/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3833737017263/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3833737017263/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3833737017263/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3833737017263/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1569306863/10000000000 : ℝ)*X 0 0+(5839835441/10000000000 : ℝ)*X 0 1+(2445755021/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((272727149/500000000 : ℝ)*X 1 0+(-418920311/2000000000 : ℝ)*X 1 1+(611438727/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((218181713/400000000 : ℝ)*X 2 0+(611438737/1250000000 : ℝ)*X 2 1+(-418920331/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((205538143/500000000 : ℝ)*X 0 0+(96061519/312500000 : ℝ)*X 0 1+(337387071/625000000 : ℝ)*X 0 2+(205538143/500000000 : ℝ)*X 1 0+(96061519/312500000 : ℝ)*X 1 1+(337387071/625000000 : ℝ)*X 1 2+(205538143/500000000 : ℝ)*X 2 0+(96061519/312500000 : ℝ)*X 2 1+(337387071/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-314425461/2000000000 : ℝ)*X 0 0+(2457768237/5000000000 : ℝ)*X 0 1+(18171733/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195537553/10000000000 : ℝ)*X 1 0+(-585578257/5000000000 : ℝ)*X 1 1+(5814954617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5195537623/10000000000 : ℝ)*X 2 0+(1162990869/2000000000 : ℝ)*X 2 1+(-1171156831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((823535353/2000000000 : ℝ)*X 0 0+(1334826687/2500000000 : ℝ)*X 0 1+(3134948867/10000000000 : ℝ)*X 0 2+(823535353/2000000000 : ℝ)*X 1 0+(1334826687/2500000000 : ℝ)*X 1 1+(3134948867/10000000000 : ℝ)*X 1 2+(823535353/2000000000 : ℝ)*X 2 0+(1334826687/2500000000 : ℝ)*X 2 1+(3134948867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49897161329344870485459/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9843063/100000000000000 : ℝ)*(base1) + (757996317/100000000000000 : ℝ)*(base19) + (728031069/100000000000000 : ℝ)*(base23) + (118833283/100000000000000 : ℝ)*(upper3) + (39672281/50000000000000 : ℝ)*(upper5) + (742374716667469/100000000000000 : ℝ)*(major0) + (742374716667469/100000000000000 : ℝ)*(major1) + (742374716667469/100000000000000 : ℝ)*(major2) + (131811646913051/12500000000000 : ℝ)*(sp0) + (527247501818311/50000000000000 : ℝ)*(sp1) + (1054495033601869/100000000000000 : ℝ)*(sp2) + (430252196911167/100000000000000 : ℝ)*(sp3) + (2596171593/100000000000000 : ℝ)*(sp4) + (665944333/50000000000000 : ℝ)*(sp7) + (26890846165181/6250000000000 : ℝ)*(f.failure) + (527247880816469/50000000000000 : ℝ)*(f.sum) + (53117879992347/25000000000000000000000000000 : ℝ)*base65 + (184528052182653/50000000000000000000000000000 : ℝ)*base68 + (210101966017347/50000000000000000000000000000 : ℝ)*base69 + (121610349982653/50000000000000000000000000000 : ℝ)*base72 + (87710071167347/25000000000000000000000000000 : ℝ)*base73 + (330568150782653/50000000000000000000000000000 : ℝ)*base76 + (5413331767347/50000000000000000000000000000 : ℝ)*base77 + (123602482882653/50000000000000000000000000000 : ℝ)*base80 + (179098035042347/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3612993/625000000000000000000 : ℝ)*base90 + (3612993/625000000000000000000 : ℝ)*base92 + (3612993/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52599602488594986039381/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53011133/6250000000000 : ℝ)*(base19) + (432739181/50000000000000 : ℝ)*(base23) + (164374481/100000000000000 : ℝ)*(base32) + (74944679/50000000000000 : ℝ)*(upper3) + (41860407/100000000000000 : ℝ)*(upper5) + (391368953862471/50000000000000 : ℝ)*(major0) + (391368953862471/50000000000000 : ℝ)*(major1) + (391368953862471/50000000000000 : ℝ)*(major2) + (2289410947/100000000000000 : ℝ)*(sp1) + (2335960423/100000000000000 : ℝ)*(sp2) + (1111829090693379/100000000000000 : ℝ)*(sp4) + (69489122069019/6250000000000 : ℝ)*(sp5) + (555912944627297/50000000000000 : ℝ)*(sp6) + (226823210058207/50000000000000 : ℝ)*(sp7) + (90729316898179/20000000000000 : ℝ)*(f.failure) + (1111829090693379/100000000000000 : ℝ)*(f.sum) + (55815899373/12500000000000000000000000000 : ℝ)*base65 + (84220471886873/25000000000000000000000000000 : ℝ)*base67 + (146146874613127/25000000000000000000000000000 : ℝ)*base70 + (54136617213127/25000000000000000000000000000 : ℝ)*base72 + (69678369449373/12500000000000000000000000000 : ℝ)*base73 + (155093601613127/25000000000000000000000000000 : ℝ)*base76 + (95618488838127/25000000000000000000000000000 : ℝ)*base78 + (104168310413127/25000000000000000000000000000 : ℝ)*base80 + (15411264099373/12500000000000000000000000000 : ℝ)*base81 + (2500913/2000000000000000000000 : ℝ)*base89 + (2500913/2000000000000000000000 : ℝ)*base91 + (2500913/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1608_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (759/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1608_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1608_s1_0 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1693643739/10000000000 : ℝ)*x 0 + (172868241/312500000 : ℝ)*x 1 + (5119165259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1693643739/10000000000 : ℝ)^4751 ≤ (10397753695457/100000000000000 : ℝ)^3727 := by
    have hnat : (1693643739 : ℕ)^4751*100000000000000^3727 ≤ 10397753695457^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693643739 10000000000 10397753695457 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172868241/312500000 : ℝ)^4751 ≤ (9402577732417/20000000000000 : ℝ)^3727 := by
    have hnat : (172868241 : ℕ)^4751*20000000000000^3727 ≤ 9402577732417^3727*312500000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172868241 312500000 9402577732417 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5119165259/10000000000 : ℝ)^4751 ≤ (4258935761881/10000000000000 : ℝ)^3727 := by
    have hnat : (5119165259 : ℕ)^4751*10000000000000^3727 ≤ 4258935761881^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119165259 10000000000 4258935761881 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1693643739/10000000000 : ℝ), (172868241/312500000 : ℝ), (5119165259/10000000000 : ℝ)] ![(10397753695457/100000000000000 : ℝ), (9402577732417/20000000000000 : ℝ), (4258935761881/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1693643739/10000000000 : ℝ)|^4751 ≤ (10397753695457/100000000000000 : ℝ)^3727
        have hw : |(-1693643739/10000000000 : ℝ)|=(1693643739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172868241/312500000 : ℝ)|^4751 ≤ (9402577732417/20000000000000 : ℝ)^3727
        have hw : |(172868241/312500000 : ℝ)|=(172868241/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5119165259/10000000000 : ℝ)|^4751 ≤ (4258935761881/10000000000000 : ℝ)^3727
        have hw : |(5119165259/10000000000 : ℝ)|=(5119165259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_1 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343140379/2500000000 : ℝ)*x 0 + (-381902071/2000000000 : ℝ)*x 1 + (1279791279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343140379/2500000000 : ℝ)^4751 ≤ (45294789636811/100000000000000 : ℝ)^3727 := by
    have hnat : (1343140379 : ℕ)^4751*100000000000000^3727 ≤ 45294789636811^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343140379 2500000000 45294789636811 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381902071/2000000000 : ℝ)^4751 ≤ (1211585423997/10000000000000 : ℝ)^3727 := by
    have hnat : (381902071 : ℕ)^4751*10000000000000^3727 ≤ 1211585423997^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381902071 2000000000 1211585423997 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279791279/2500000000 : ℝ)^4751 ≤ (10647339025559/25000000000000 : ℝ)^3727 := by
    have hnat : (1279791279 : ℕ)^4751*25000000000000^3727 ≤ 10647339025559^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279791279 2500000000 10647339025559 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343140379/2500000000 : ℝ), (-381902071/2000000000 : ℝ), (1279791279/2500000000 : ℝ)] ![(45294789636811/100000000000000 : ℝ), (1211585423997/10000000000000 : ℝ), (10647339025559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343140379/2500000000 : ℝ)|^4751 ≤ (45294789636811/100000000000000 : ℝ)^3727
        have hw : |(1343140379/2500000000 : ℝ)|=(1343140379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381902071/2000000000 : ℝ)|^4751 ≤ (1211585423997/10000000000000 : ℝ)^3727
        have hw : |(-381902071/2000000000 : ℝ)|=(381902071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279791279/2500000000 : ℝ)|^4751 ≤ (10647339025559/25000000000000 : ℝ)^3727
        have hw : |(1279791279/2500000000 : ℝ)|=(1279791279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_2 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686280599/5000000000 : ℝ)*x 0 + (2559582689/5000000000 : ℝ)*x 1 + (-381902087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686280599/5000000000 : ℝ)^4751 ≤ (5661848277403/12500000000000 : ℝ)^3727 := by
    have hnat : (2686280599 : ℕ)^4751*12500000000000^3727 ≤ 5661848277403^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686280599 5000000000 5661848277403 12500000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559582689/5000000000 : ℝ)^4751 ≤ (21294679440427/50000000000000 : ℝ)^3727 := by
    have hnat : (2559582689 : ℕ)^4751*50000000000000^3727 ≤ 21294679440427^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559582689 5000000000 21294679440427 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381902087/2000000000 : ℝ)^4751 ≤ (6057927443517/50000000000000 : ℝ)^3727 := by
    have hnat : (381902087 : ℕ)^4751*50000000000000^3727 ≤ 6057927443517^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381902087 2000000000 6057927443517 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686280599/5000000000 : ℝ), (2559582689/5000000000 : ℝ), (-381902087/2000000000 : ℝ)] ![(5661848277403/12500000000000 : ℝ), (21294679440427/50000000000000 : ℝ), (6057927443517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686280599/5000000000 : ℝ)|^4751 ≤ (5661848277403/12500000000000 : ℝ)^3727
        have hw : |(2686280599/5000000000 : ℝ)|=(2686280599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2559582689/5000000000 : ℝ)|^4751 ≤ (21294679440427/50000000000000 : ℝ)^3727
        have hw : |(2559582689/5000000000 : ℝ)|=(2559582689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381902087/2000000000 : ℝ)|^4751 ≤ (6057927443517/50000000000000 : ℝ)^3727
        have hw : |(-381902087/2000000000 : ℝ)|=(381902087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_3 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202736631/10000000000 : ℝ)*x 0 + (1860261743/5000000000 : ℝ)*x 1 + (1182949581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202736631/10000000000 : ℝ)^4751 ≤ (16560252830671/50000000000000 : ℝ)^3727 := by
    have hnat : (4202736631 : ℕ)^4751*50000000000000^3727 ≤ 16560252830671^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202736631 10000000000 16560252830671 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1860261743/5000000000 : ℝ)^4751 ≤ (14177404805467/50000000000000 : ℝ)^3727 := by
    have hnat : (1860261743 : ℕ)^4751*50000000000000^3727 ≤ 14177404805467^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860261743 5000000000 14177404805467 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182949581/2500000000 : ℝ)^4751 ≤ (38524684715643/100000000000000 : ℝ)^3727 := by
    have hnat : (1182949581 : ℕ)^4751*100000000000000^3727 ≤ 38524684715643^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182949581 2500000000 38524684715643 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202736631/10000000000 : ℝ), (1860261743/5000000000 : ℝ), (1182949581/2500000000 : ℝ)] ![(16560252830671/50000000000000 : ℝ), (14177404805467/50000000000000 : ℝ), (38524684715643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202736631/10000000000 : ℝ)|^4751 ≤ (16560252830671/50000000000000 : ℝ)^3727
        have hw : |(4202736631/10000000000 : ℝ)|=(4202736631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1860261743/5000000000 : ℝ)|^4751 ≤ (14177404805467/50000000000000 : ℝ)^3727
        have hw : |(1860261743/5000000000 : ℝ)|=(1860261743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1182949581/2500000000 : ℝ)|^4751 ≤ (38524684715643/100000000000000 : ℝ)^3727
        have hw : |(1182949581/2500000000 : ℝ)|=(1182949581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_4 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1693870743/10000000000 : ℝ)*x 0 + (204946903/400000000 : ℝ)*x 1 + (5527206341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1693870743/10000000000 : ℝ)^4751 ≤ (10399530274801/100000000000000 : ℝ)^3727 := by
    have hnat : (1693870743 : ℕ)^4751*100000000000000^3727 ≤ 10399530274801^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693870743 10000000000 10399530274801 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204946903/400000000 : ℝ)^4751 ≤ (8527433069267/20000000000000 : ℝ)^3727 := by
    have hnat : (204946903 : ℕ)^4751*20000000000000^3727 ≤ 8527433069267^3727*400000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204946903 400000000 8527433069267 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527206341/10000000000 : ℝ)^4751 ≤ (2935206523131/6250000000000 : ℝ)^3727 := by
    have hnat : (5527206341 : ℕ)^4751*6250000000000^3727 ≤ 2935206523131^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527206341 10000000000 2935206523131 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1693870743/10000000000 : ℝ), (204946903/400000000 : ℝ), (5527206341/10000000000 : ℝ)] ![(10399530274801/100000000000000 : ℝ), (8527433069267/20000000000000 : ℝ), (2935206523131/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1693870743/10000000000 : ℝ)|^4751 ≤ (10399530274801/100000000000000 : ℝ)^3727
        have hw : |(-1693870743/10000000000 : ℝ)|=(1693870743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(204946903/400000000 : ℝ)|^4751 ≤ (8527433069267/20000000000000 : ℝ)^3727
        have hw : |(204946903/400000000 : ℝ)|=(204946903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527206341/10000000000 : ℝ)|^4751 ≤ (2935206523131/6250000000000 : ℝ)^3727
        have hw : |(5527206341/10000000000 : ℝ)|=(5527206341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_5 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631413771/5000000000 : ℝ)*x 0 + (-1501468873/10000000000 : ℝ)*x 1 + (690900833/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631413771/5000000000 : ℝ)^4751 ≤ (1102969748273/2500000000000 : ℝ)^3727 := by
    have hnat : (2631413771 : ℕ)^4751*2500000000000^3727 ≤ 1102969748273^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631413771 5000000000 1102969748273 2500000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501468873/10000000000 : ℝ)^4751 ≤ (4458951091159/50000000000000 : ℝ)^3727 := by
    have hnat : (1501468873 : ℕ)^4751*50000000000000^3727 ≤ 4458951091159^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501468873 10000000000 4458951091159 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690900833/1250000000 : ℝ)^4751 ≤ (4696330786859/10000000000000 : ℝ)^3727 := by
    have hnat : (690900833 : ℕ)^4751*10000000000000^3727 ≤ 4696330786859^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690900833 1250000000 4696330786859 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631413771/5000000000 : ℝ), (-1501468873/10000000000 : ℝ), (690900833/1250000000 : ℝ)] ![(1102969748273/2500000000000 : ℝ), (4458951091159/50000000000000 : ℝ), (4696330786859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631413771/5000000000 : ℝ)|^4751 ≤ (1102969748273/2500000000000 : ℝ)^3727
        have hw : |(2631413771/5000000000 : ℝ)|=(2631413771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1501468873/10000000000 : ℝ)|^4751 ≤ (4458951091159/50000000000000 : ℝ)^3727
        have hw : |(-1501468873/10000000000 : ℝ)|=(1501468873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690900833/1250000000 : ℝ)|^4751 ≤ (4696330786859/10000000000000 : ℝ)^3727
        have hw : |(690900833/1250000000 : ℝ)|=(690900833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_6 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631413457/5000000000 : ℝ)*x 0 + (5527206901/10000000000 : ℝ)*x 1 + (-75073471/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631413457/5000000000 : ℝ)^4751 ≤ (44118783219881/100000000000000 : ℝ)^3727 := by
    have hnat : (2631413457 : ℕ)^4751*100000000000000^3727 ≤ 44118783219881^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631413457 5000000000 44118783219881 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527206901/10000000000 : ℝ)^4751 ≤ (46963310435597/100000000000000 : ℝ)^3727 := by
    have hnat : (5527206901 : ℕ)^4751*100000000000000^3727 ≤ 46963310435597^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527206901 10000000000 46963310435597 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75073471/500000000 : ℝ)^4751 ≤ (4458953161917/50000000000000 : ℝ)^3727 := by
    have hnat : (75073471 : ℕ)^4751*50000000000000^3727 ≤ 4458953161917^3727*500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75073471 500000000 4458953161917 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631413457/5000000000 : ℝ), (5527206901/10000000000 : ℝ), (-75073471/500000000 : ℝ)] ![(44118783219881/100000000000000 : ℝ), (46963310435597/100000000000000 : ℝ), (4458953161917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631413457/5000000000 : ℝ)|^4751 ≤ (44118783219881/100000000000000 : ℝ)^3727
        have hw : |(2631413457/5000000000 : ℝ)|=(2631413457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527206901/10000000000 : ℝ)|^4751 ≤ (46963310435597/100000000000000 : ℝ)^3727
        have hw : |(5527206901/10000000000 : ℝ)|=(5527206901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75073471/500000000 : ℝ)|^4751 ≤ (4458953161917/50000000000000 : ℝ)^3727
        have hw : |(-75073471/500000000 : ℝ)|=(75073471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s1_7 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2101645921/5000000000 : ℝ)*x 0 + (590094079/1250000000 : ℝ)*x 1 + (3731740959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101645921/5000000000 : ℝ)^4751 ≤ (16563041688457/50000000000000 : ℝ)^3727 := by
    have hnat : (2101645921 : ℕ)^4751*50000000000000^3727 ≤ 16563041688457^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101645921 5000000000 16563041688457 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590094079/1250000000 : ℝ)^4751 ≤ (38410082751361/100000000000000 : ℝ)^3727 := by
    have hnat : (590094079 : ℕ)^4751*100000000000000^3727 ≤ 38410082751361^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590094079 1250000000 38410082751361 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3731740959/10000000000 : ℝ)^4751 ≤ (14231916925579/50000000000000 : ℝ)^3727 := by
    have hnat : (3731740959 : ℕ)^4751*50000000000000^3727 ≤ 14231916925579^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731740959 10000000000 14231916925579 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101645921/5000000000 : ℝ), (590094079/1250000000 : ℝ), (3731740959/10000000000 : ℝ)] ![(16563041688457/50000000000000 : ℝ), (38410082751361/100000000000000 : ℝ), (14231916925579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101645921/5000000000 : ℝ)|^4751 ≤ (16563041688457/50000000000000 : ℝ)^3727
        have hw : |(2101645921/5000000000 : ℝ)|=(2101645921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(590094079/1250000000 : ℝ)|^4751 ≤ (38410082751361/100000000000000 : ℝ)^3727
        have hw : |(590094079/1250000000 : ℝ)|=(590094079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3731740959/10000000000 : ℝ)|^4751 ≤ (14231916925579/50000000000000 : ℝ)^3727
        have hw : |(3731740959/10000000000 : ℝ)|=(3731740959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1608_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (759/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1819/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8919/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (759/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (759/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (759/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (759/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (759/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (759/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3979/100000 : ℝ) ^ (4747/1024 : ℝ) ≤ (1613923636353/5000000000000000000 : ℝ) := by
    have hpowers : (3979/100000 : ℝ)^4747 ≤ (1613923636353/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3979 : ℕ)^4747*5000000000000000000^1024 ≤ 1613923636353^1024*100000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3979 100000 1613923636353 5000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3979/100000 : ℝ)) (X := (1613923636353/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (759/3125 : ℝ) ^ (4747/1024 : ℝ) ≤ (70762738323686701/50000000000000000000 : ℝ) := by
    have hpowers : (759/3125 : ℝ)^4747 ≤ (70762738323686701/50000000000000000000 : ℝ)^1024 := by
      have hnat : (759 : ℕ)^4747*50000000000000000000^1024 ≤ 70762738323686701^1024*3125^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        759 3125 70762738323686701 50000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (759/3125 : ℝ)) (X := (70762738323686701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001613923636353/2500000000000000000 : ℝ) ≤ (5000000696295507/5000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (2500001613923636353/2500000000000000000 : ℝ)^1024 ≤ (5000000696295507/5000000000000000 : ℝ)^4747 := by
      have hnat : (2500001613923636353 : ℕ)^1024*5000000000000000^4747 ≤ 5000000696295507^4747*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001613923636353 2500000000000000000 5000000696295507 5000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000696295507/5000000000000000 : ℝ)) (X := (2500001613923636353/2500000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50070778877560050231/50000000000000000000 : ℝ) ≤ (5001525961061369/5000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (50070778877560050231/50000000000000000000 : ℝ)^1024 ≤ (5001525961061369/5000000000000000 : ℝ)^4747 := by
      have hnat : (50070778877560050231 : ℕ)^1024*5000000000000000^4747 ≤ 5001525961061369^4747*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070778877560050231 50000000000000000000 5001525961061369 5000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001525961061369/5000000000000000 : ℝ)) (X := (50070778877560050231/50000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25070762738323686701/25000000000000000000 : ℝ) ≤ (5003051225827231/5000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (25070762738323686701/25000000000000000000 : ℝ)^1024 ≤ (5003051225827231/5000000000000000 : ℝ)^4747 := by
      have hnat : (25070762738323686701 : ℕ)^1024*5000000000000000^4747 ≤ 5003051225827231^4747*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25070762738323686701 25000000000000000000 5003051225827231 5000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003051225827231/5000000000000000 : ℝ)) (X := (25070762738323686701/25000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1613923636353/5000000000000000000 : ℝ) ≤ ((4414472873219944429/4415000000000000000 : ℝ)+2*(762632382931/507725000000000 : ℝ)*(3979/100000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (4414472873219944429/4415000000000000000 : ℝ)+2*(762632382931/507725000000000 : ℝ)*(3979/100000 : ℝ)=(5000000696295507/5000000000000000 : ℝ) by norm_num, show 1+2*(1613923636353/5000000000000000000 : ℝ)=(2500001613923636353/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70762738323686701/50000000000000000000 : ℝ)+(1613923636353/5000000000000000000 : ℝ) ≤ ((4414472873219944429/4415000000000000000 : ℝ)+(762632382931/507725000000000 : ℝ)*((759/3125 : ℝ)+(3979/100000 : ℝ)))^(4747/1024 : ℝ) := by
    rw [show (4414472873219944429/4415000000000000000 : ℝ)+(762632382931/507725000000000 : ℝ)*((759/3125 : ℝ)+(3979/100000 : ℝ))=(5001525961061369/5000000000000000 : ℝ) by norm_num, show 1+(70762738323686701/50000000000000000000 : ℝ)+(1613923636353/5000000000000000000 : ℝ)=(50070778877560050231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70762738323686701/50000000000000000000 : ℝ) ≤ ((4414472873219944429/4415000000000000000 : ℝ)+2*(762632382931/507725000000000 : ℝ)*(759/3125 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (4414472873219944429/4415000000000000000 : ℝ)+2*(762632382931/507725000000000 : ℝ)*(759/3125 : ℝ)=(5003051225827231/5000000000000000 : ℝ) by norm_num, show 1+2*(70762738323686701/50000000000000000000 : ℝ)=(25070762738323686701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4414472873219944429/4415000000000000000 : ℝ)*(X 1 0+X 2 0)+(762632382931/507725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (3979/100000 : ℝ)) (hi := (759/3125 : ℝ)) (c := (4414472873219944429/4415000000000000000 : ℝ)) (alpha := (762632382931/507725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4414472873219944429/4415000000000000000 : ℝ)*(X 0 1+X 2 1)+(762632382931/507725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (3979/100000 : ℝ)) (hi := (759/3125 : ℝ)) (c := (4414472873219944429/4415000000000000000 : ℝ)) (alpha := (762632382931/507725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4414472873219944429/4415000000000000000 : ℝ)*(X 0 2+X 1 2)+(762632382931/507725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (3979/100000 : ℝ)) (hi := (759/3125 : ℝ)) (c := (4414472873219944429/4415000000000000000 : ℝ)) (alpha := (762632382931/507725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1693643739/10000000000 : ℝ)*X 0 0+(172868241/312500000 : ℝ)*X 0 1+(5119165259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343140379/2500000000 : ℝ)*X 1 0+(-381902071/2000000000 : ℝ)*X 1 1+(1279791279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686280599/5000000000 : ℝ)*X 2 0+(2559582689/5000000000 : ℝ)*X 2 1+(-381902087/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4202736631/10000000000 : ℝ)*X 0 0+(1860261743/5000000000 : ℝ)*X 0 1+(1182949581/2500000000 : ℝ)*X 0 2+(4202736631/10000000000 : ℝ)*X 1 0+(1860261743/5000000000 : ℝ)*X 1 1+(1182949581/2500000000 : ℝ)*X 1 2+(4202736631/10000000000 : ℝ)*X 2 0+(1860261743/5000000000 : ℝ)*X 2 1+(1182949581/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1693870743/10000000000 : ℝ)*X 0 0+(204946903/400000000 : ℝ)*X 0 1+(5527206341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2631413771/5000000000 : ℝ)*X 1 0+(-1501468873/10000000000 : ℝ)*X 1 1+(690900833/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631413457/5000000000 : ℝ)*X 2 0+(5527206901/10000000000 : ℝ)*X 2 1+(-75073471/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2101645921/5000000000 : ℝ)*X 0 0+(590094079/1250000000 : ℝ)*X 0 1+(3731740959/10000000000 : ℝ)*X 0 2+(2101645921/5000000000 : ℝ)*X 1 0+(590094079/1250000000 : ℝ)*X 1 1+(3731740959/10000000000 : ℝ)*X 1 2+(2101645921/5000000000 : ℝ)*X 2 0+(590094079/1250000000 : ℝ)*X 2 1+(3731740959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (625110260170786613634556119/253862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78360529/100000000000000 : ℝ)*(base1) + (750719921/100000000000000 : ℝ)*(base19) + (303635227/50000000000000 : ℝ)*(base23) + (47466337/50000000000000 : ℝ)*(upper3) + (24536429/100000000000000 : ℝ)*(upper5) + (85310330397781/5000000000000 : ℝ)*(major0) + (85310330397781/5000000000000 : ℝ)*(major1) + (85310330397781/5000000000000 : ℝ)*(major2) + (151472046524681/6250000000000 : ℝ)*(sp0) + (1211778368081199/50000000000000 : ℝ)*(sp1) + (1211778439805933/50000000000000 : ℝ)*(sp2) + (247213268350311/25000000000000 : ℝ)*(sp3) + (2410423977/50000000000000 : ℝ)*(sp4) + (2495187237/100000000000000 : ℝ)*(sp7) + (98885564694901/10000000000000 : ℝ)*(f.failure) + (30294468586029/1250000000000 : ℝ)*(f.sum) + (3524668068737/1269312500000000000000000000 : ℝ)*base66 + (3017389508470572873/507725000000000000000000000000000 : ℝ)*base68 + (509167003788647873/507725000000000000000000000000000 : ℝ)*base70 + (2390341224530827127/507725000000000000000000000000000 : ℝ)*base71 + (87937481776663/10154500000000000000000000000 : ℝ)*base74 + (2218984737183602127/507725000000000000000000000000000 : ℝ)*base75 + (587460471258327127/507725000000000000000000000000000 : ℝ)*base77 + (353000819219077127/507725000000000000000000000000000 : ℝ)*base79 + (20907069470717/4061800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (8646153/1000000000000000000000 : ℝ)*base90 + (8646153/1000000000000000000000 : ℝ)*base92 + (8646153/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14787414425681659934754267/1379687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (523143903/25000000000000 : ℝ)*(base19) + (908494147/50000000000000 : ℝ)*(base23) + (2801043/12500000000000 : ℝ)*(upper2) + (36788141/10000000000000 : ℝ)*(upper3) + (157882001/100000000000000 : ℝ)*(upper5) + (10903794452847/625000000000 : ℝ)*(major0) + (10903794452847/625000000000 : ℝ)*(major1) + (10903794452847/625000000000 : ℝ)*(major2) + (15883851399/100000000000000 : ℝ)*(sp1) + (14806616967/100000000000000 : ℝ)*(sp2) + (61952566924991/2500000000000 : ℝ)*(sp4) + (619521175143157/25000000000000 : ℝ)*(sp5) + (1239043026697189/50000000000000 : ℝ)*(sp6) + (126388898830821/12500000000000 : ℝ)*(sp7) + (126388898830821/12500000000000 : ℝ)*(f.failure) + (61952566924991/2500000000000 : ℝ)*(f.sum) + (188064412233/110375000000000000000000000 : ℝ)*base65 + (18022421941135637/2759375000000000000000000000000 : ℝ)*base68 + (25270902649910637/2759375000000000000000000000000 : ℝ)*base70 + (1505188234323137/2759375000000000000000000000000 : ℝ)*base72 + (1158662460069/883000000000000000000000000 : ℝ)*base74 + (21196611058623137/2759375000000000000000000000000 : ℝ)*base76 + (7596383541616887/2759375000000000000000000000000 : ℝ)*base78 + (3058602021860637/2759375000000000000000000000000 : ℝ)*base80 + (5060361509329/883000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (8262087/1250000000000000000000 : ℝ)*base89 + (8262087/1250000000000000000000 : ℝ)*base91 + (8262087/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1608_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (759/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1819/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1608_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1608_s2_0 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-853911869/5000000000 : ℝ)*x 0 + (5467596233/10000000000 : ℝ)*x 1 + (5174073119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853911869/5000000000 : ℝ)^4751 ≤ (2101770916413/20000000000000 : ℝ)^3727 := by
    have hnat : (853911869 : ℕ)^4751*20000000000000^3727 ≤ 2101770916413^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853911869 5000000000 2101770916413 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467596233/10000000000 : ℝ)^4751 ≤ (23159305719463/50000000000000 : ℝ)^3727 := by
    have hnat : (5467596233 : ℕ)^4751*50000000000000^3727 ≤ 23159305719463^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467596233 10000000000 23159305719463 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174073119/10000000000 : ℝ)^4751 ≤ (43172533966349/100000000000000 : ℝ)^3727 := by
    have hnat : (5174073119 : ℕ)^4751*100000000000000^3727 ≤ 43172533966349^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174073119 10000000000 43172533966349 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-853911869/5000000000 : ℝ), (5467596233/10000000000 : ℝ), (5174073119/10000000000 : ℝ)] ![(2101770916413/20000000000000 : ℝ), (23159305719463/50000000000000 : ℝ), (43172533966349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-853911869/5000000000 : ℝ)|^4751 ≤ (2101770916413/20000000000000 : ℝ)^3727
        have hw : |(-853911869/5000000000 : ℝ)|=(853911869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467596233/10000000000 : ℝ)|^4751 ≤ (23159305719463/50000000000000 : ℝ)^3727
        have hw : |(5467596233/10000000000 : ℝ)|=(5467596233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174073119/10000000000 : ℝ)|^4751 ≤ (43172533966349/100000000000000 : ℝ)^3727
        have hw : |(5174073119/10000000000 : ℝ)|=(5174073119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_1 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071170019/2000000000 : ℝ)*x 0 + (-1859422919/10000000000 : ℝ)*x 1 + (5174072981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071170019/2000000000 : ℝ)^4751 ≤ (4511526663131/10000000000000 : ℝ)^3727 := by
    have hnat : (1071170019 : ℕ)^4751*10000000000000^3727 ≤ 4511526663131^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071170019 2000000000 4511526663131 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1859422919/10000000000 : ℝ)^4751 ≤ (5856100424359/50000000000000 : ℝ)^3727 := by
    have hnat : (1859422919 : ℕ)^4751*50000000000000^3727 ≤ 5856100424359^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859422919 10000000000 5856100424359 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174072981/10000000000 : ℝ)^4751 ≤ (21586266249253/50000000000000 : ℝ)^3727 := by
    have hnat : (5174072981 : ℕ)^4751*50000000000000^3727 ≤ 21586266249253^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174072981 10000000000 21586266249253 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071170019/2000000000 : ℝ), (-1859422919/10000000000 : ℝ), (5174072981/10000000000 : ℝ)] ![(4511526663131/10000000000000 : ℝ), (5856100424359/50000000000000 : ℝ), (21586266249253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071170019/2000000000 : ℝ)|^4751 ≤ (4511526663131/10000000000000 : ℝ)^3727
        have hw : |(1071170019/2000000000 : ℝ)|=(1071170019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1859422919/10000000000 : ℝ)|^4751 ≤ (5856100424359/50000000000000 : ℝ)^3727
        have hw : |(-1859422919/10000000000 : ℝ)|=(1859422919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174072981/10000000000 : ℝ)|^4751 ≤ (21586266249253/50000000000000 : ℝ)^3727
        have hw : |(5174072981/10000000000 : ℝ)|=(5174072981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_2 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338962497/2500000000 : ℝ)*x 0 + (5174073089/10000000000 : ℝ)*x 1 + (-46485573/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338962497/2500000000 : ℝ)^4751 ≤ (45115265482351/100000000000000 : ℝ)^3727 := by
    have hnat : (1338962497 : ℕ)^4751*100000000000000^3727 ≤ 45115265482351^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338962497 2500000000 45115265482351 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174073089/10000000000 : ℝ)^4751 ≤ (43172533647253/100000000000000 : ℝ)^3727 := by
    have hnat : (5174073089 : ℕ)^4751*100000000000000^3727 ≤ 43172533647253^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174073089 10000000000 43172533647253 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46485573/250000000 : ℝ)^4751 ≤ (2928050214187/25000000000000 : ℝ)^3727 := by
    have hnat : (46485573 : ℕ)^4751*25000000000000^3727 ≤ 2928050214187^3727*250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46485573 250000000 2928050214187 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338962497/2500000000 : ℝ), (5174073089/10000000000 : ℝ), (-46485573/250000000 : ℝ)] ![(45115265482351/100000000000000 : ℝ), (43172533647253/100000000000000 : ℝ), (2928050214187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338962497/2500000000 : ℝ)|^4751 ≤ (45115265482351/100000000000000 : ℝ)^3727
        have hw : |(1338962497/2500000000 : ℝ)|=(1338962497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174073089/10000000000 : ℝ)|^4751 ≤ (43172533647253/100000000000000 : ℝ)^3727
        have hw : |(5174073089/10000000000 : ℝ)|=(5174073089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46485573/250000000 : ℝ)|^4751 ≤ (2928050214187/25000000000000 : ℝ)^3727
        have hw : |(-46485573/250000000 : ℝ)|=(46485573/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_3 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526649367/1250000000 : ℝ)*x 0 + (966339493/2500000000 : ℝ)*x 1 + (916949033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526649367/1250000000 : ℝ)^4751 ≤ (33225605022119/100000000000000 : ℝ)^3727 := by
    have hnat : (526649367 : ℕ)^4751*100000000000000^3727 ≤ 33225605022119^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526649367 1250000000 33225605022119 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966339493/2500000000 : ℝ)^4751 ≤ (232573044803/781250000000 : ℝ)^3727 := by
    have hnat : (966339493 : ℕ)^4751*781250000000^3727 ≤ 232573044803^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966339493 2500000000 232573044803 781250000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (916949033/2000000000 : ℝ)^4751 ≤ (4625630653137/12500000000000 : ℝ)^3727 := by
    have hnat : (916949033 : ℕ)^4751*12500000000000^3727 ≤ 4625630653137^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916949033 2000000000 4625630653137 12500000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526649367/1250000000 : ℝ), (966339493/2500000000 : ℝ), (916949033/2000000000 : ℝ)] ![(33225605022119/100000000000000 : ℝ), (232573044803/781250000000 : ℝ), (4625630653137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526649367/1250000000 : ℝ)|^4751 ≤ (33225605022119/100000000000000 : ℝ)^3727
        have hw : |(526649367/1250000000 : ℝ)|=(526649367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(966339493/2500000000 : ℝ)|^4751 ≤ (232573044803/781250000000 : ℝ)^3727
        have hw : |(966339493/2500000000 : ℝ)|=(966339493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(916949033/2000000000 : ℝ)|^4751 ≤ (4625630653137/12500000000000 : ℝ)^3727
        have hw : |(916949033/2000000000 : ℝ)|=(916949033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_4 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-426976299/2500000000 : ℝ)*x 0 + (5176361419/10000000000 : ℝ)*x 1 + (5465282923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426976299/2500000000 : ℝ)^4751 ≤ (656843346461/6250000000000 : ℝ)^3727 := by
    have hnat : (426976299 : ℕ)^4751*6250000000000^3727 ≤ 656843346461^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426976299 2500000000 656843346461 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176361419/10000000000 : ℝ)^4751 ≤ (43196875052799/100000000000000 : ℝ)^3727 := by
    have hnat : (5176361419 : ℕ)^4751*100000000000000^3727 ≤ 43196875052799^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176361419 10000000000 43196875052799 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465282923/10000000000 : ℝ)^4751 ≤ (46293631387801/100000000000000 : ℝ)^3727 := by
    have hnat : (5465282923 : ℕ)^4751*100000000000000^3727 ≤ 46293631387801^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465282923 10000000000 46293631387801 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426976299/2500000000 : ℝ), (5176361419/10000000000 : ℝ), (5465282923/10000000000 : ℝ)] ![(656843346461/6250000000000 : ℝ), (43196875052799/100000000000000 : ℝ), (46293631387801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426976299/2500000000 : ℝ)|^4751 ≤ (656843346461/6250000000000 : ℝ)^3727
        have hw : |(-426976299/2500000000 : ℝ)|=(426976299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176361419/10000000000 : ℝ)|^4751 ≤ (43196875052799/100000000000000 : ℝ)^3727
        have hw : |(5176361419/10000000000 : ℝ)|=(5176361419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465282923/10000000000 : ℝ)|^4751 ≤ (46293631387801/100000000000000 : ℝ)^3727
        have hw : |(5465282923/10000000000 : ℝ)|=(5465282923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_5 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638956831/5000000000 : ℝ)*x 0 + (-784106559/5000000000 : ℝ)*x 1 + (5465283041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638956831/5000000000 : ℝ)^4751 ≤ (8856013837999/20000000000000 : ℝ)^3727 := by
    have hnat : (2638956831 : ℕ)^4751*20000000000000^3727 ≤ 8856013837999^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638956831 5000000000 8856013837999 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (784106559/5000000000 : ℝ)^4751 ≤ (377051925441/4000000000000 : ℝ)^3727 := by
    have hnat : (784106559 : ℕ)^4751*4000000000000^3727 ≤ 377051925441^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784106559 5000000000 377051925441 4000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465283041/10000000000 : ℝ)^4751 ≤ (46293632661939/100000000000000 : ℝ)^3727 := by
    have hnat : (5465283041 : ℕ)^4751*100000000000000^3727 ≤ 46293632661939^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465283041 10000000000 46293632661939 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638956831/5000000000 : ℝ), (-784106559/5000000000 : ℝ), (5465283041/10000000000 : ℝ)] ![(8856013837999/20000000000000 : ℝ), (377051925441/4000000000000 : ℝ), (46293632661939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638956831/5000000000 : ℝ)|^4751 ≤ (8856013837999/20000000000000 : ℝ)^3727
        have hw : |(2638956831/5000000000 : ℝ)|=(2638956831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-784106559/5000000000 : ℝ)|^4751 ≤ (377051925441/4000000000000 : ℝ)^3727
        have hw : |(-784106559/5000000000 : ℝ)|=(784106559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465283041/10000000000 : ℝ)|^4751 ≤ (46293632661939/100000000000000 : ℝ)^3727
        have hw : |(5465283041/10000000000 : ℝ)|=(5465283041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_6 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638956953/5000000000 : ℝ)*x 0 + (5465282541/10000000000 : ℝ)*x 1 + (-1568213483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638956953/5000000000 : ℝ)^4751 ≤ (276750448747/625000000000 : ℝ)^3727 := by
    have hnat : (2638956953 : ℕ)^4751*625000000000^3727 ≤ 276750448747^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638956953 5000000000 276750448747 625000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465282541/10000000000 : ℝ)^4751 ≤ (11573406815763/25000000000000 : ℝ)^3727 := by
    have hnat : (5465282541 : ℕ)^4751*25000000000000^3727 ≤ 11573406815763^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465282541 10000000000 11573406815763 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568213483/10000000000 : ℝ)^4751 ≤ (4713150466391/50000000000000 : ℝ)^3727 := by
    have hnat : (1568213483 : ℕ)^4751*50000000000000^3727 ≤ 4713150466391^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568213483 10000000000 4713150466391 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638956953/5000000000 : ℝ), (5465282541/10000000000 : ℝ), (-1568213483/10000000000 : ℝ)] ![(276750448747/625000000000 : ℝ), (11573406815763/25000000000000 : ℝ), (4713150466391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638956953/5000000000 : ℝ)|^4751 ≤ (276750448747/625000000000 : ℝ)^3727
        have hw : |(2638956953/5000000000 : ℝ)|=(2638956953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465282541/10000000000 : ℝ)|^4751 ≤ (11573406815763/25000000000000 : ℝ)^3727
        have hw : |(5465282541/10000000000 : ℝ)|=(5465282541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1568213483/10000000000 : ℝ)|^4751 ≤ (4713150466391/50000000000000 : ℝ)^3727
        have hw : |(-1568213483/10000000000 : ℝ)|=(1568213483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s2_7 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213395399/10000000000 : ℝ)*x 0 + (4579137263/10000000000 : ℝ)*x 1 + (1935513861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213395399/10000000000 : ℝ)^4751 ≤ (16613810124729/50000000000000 : ℝ)^3727 := by
    have hnat : (4213395399 : ℕ)^4751*50000000000000^3727 ≤ 16613810124729^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213395399 10000000000 16613810124729 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4579137263/10000000000 : ℝ)^4751 ≤ (36947355457733/100000000000000 : ℝ)^3727 := by
    have hnat : (4579137263 : ℕ)^4751*100000000000000^3727 ≤ 36947355457733^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579137263 10000000000 36947355457733 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935513861/5000000000 : ℝ)^4751 ≤ (14912512138057/50000000000000 : ℝ)^3727 := by
    have hnat : (1935513861 : ℕ)^4751*50000000000000^3727 ≤ 14912512138057^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935513861 5000000000 14912512138057 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213395399/10000000000 : ℝ), (4579137263/10000000000 : ℝ), (1935513861/5000000000 : ℝ)] ![(16613810124729/50000000000000 : ℝ), (36947355457733/100000000000000 : ℝ), (14912512138057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213395399/10000000000 : ℝ)|^4751 ≤ (16613810124729/50000000000000 : ℝ)^3727
        have hw : |(4213395399/10000000000 : ℝ)|=(4213395399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4579137263/10000000000 : ℝ)|^4751 ≤ (36947355457733/100000000000000 : ℝ)^3727
        have hw : |(4579137263/10000000000 : ℝ)|=(4579137263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1935513861/5000000000 : ℝ)|^4751 ≤ (14912512138057/50000000000000 : ℝ)^3727
        have hw : |(1935513861/5000000000 : ℝ)|=(1935513861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1608_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1819/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (257/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8251/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8919/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1819/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8919/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1819/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8919/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1819/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8919/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1819/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8919/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1819/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8919/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1819/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1819/20000 : ℝ) ^ (4747/1024 : ℝ) ≤ (93144621870157/6250000000000000000 : ℝ) := by
    have hpowers : (1819/20000 : ℝ)^4747 ≤ (93144621870157/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1819 : ℕ)^4747*6250000000000000000^1024 ≤ 93144621870157^1024*20000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1819 20000 93144621870157 6250000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1819/20000 : ℝ)) (X := (93144621870157/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8919/50000 : ℝ) ^ (4747/1024 : ℝ) ≤ (16920134559836559/50000000000000000000 : ℝ) := by
    have hpowers : (8919/50000 : ℝ)^4747 ≤ (16920134559836559/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8919 : ℕ)^4747*50000000000000000000^1024 ≤ 16920134559836559^1024*50000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8919 50000 16920134559836559 50000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8919/50000 : ℝ)) (X := (16920134559836559/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125093144621870157/3125000000000000000 : ℝ) ≤ (10000064295919433/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (3125093144621870157/3125000000000000000 : ℝ)^1024 ≤ (10000064295919433/10000000000000000 : ℝ)^4747 := by
      have hnat : (3125093144621870157 : ℕ)^1024*10000000000000000^4747 ≤ 10000064295919433^4747*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125093144621870157 3125000000000000000 10000064295919433 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064295919433/10000000000000000 : ℝ)) (X := (3125093144621870157/3125000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003533058306959563/10000000000000000000 : ℝ) ≤ (10000762028770177/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (10003533058306959563/10000000000000000000 : ℝ)^1024 ≤ (10000762028770177/10000000000000000 : ℝ)^4747 := by
      have hnat : (10003533058306959563 : ℕ)^1024*10000000000000000^4747 ≤ 10000762028770177^4747*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003533058306959563 10000000000000000000 10000762028770177 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000762028770177/10000000000000000 : ℝ)) (X := (10003533058306959563/10000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016920134559836559/25000000000000000000 : ℝ) ≤ (10001459761620921/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (25016920134559836559/25000000000000000000 : ℝ)^1024 ≤ (10001459761620921/10000000000000000 : ℝ)^4747 := by
      have hnat : (25016920134559836559 : ℕ)^1024*10000000000000000^4747 ≤ 10001459761620921^4747*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016920134559836559 25000000000000000000 10001459761620921 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001459761620921/10000000000000000 : ℝ)) (X := (25016920134559836559/25000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(93144621870157/6250000000000000000 : ℝ) ≤ ((87417870378668569359/87430000000000000000 : ℝ)+2*(87216606343/109287500000000 : ℝ)*(1819/20000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (87417870378668569359/87430000000000000000 : ℝ)+2*(87216606343/109287500000000 : ℝ)*(1819/20000 : ℝ)=(10000064295919433/10000000000000000 : ℝ) by norm_num, show 1+2*(93144621870157/6250000000000000000 : ℝ)=(3125093144621870157/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16920134559836559/50000000000000000000 : ℝ)+(93144621870157/6250000000000000000 : ℝ) ≤ ((87417870378668569359/87430000000000000000 : ℝ)+(87216606343/109287500000000 : ℝ)*((8919/50000 : ℝ)+(1819/20000 : ℝ)))^(4747/1024 : ℝ) := by
    rw [show (87417870378668569359/87430000000000000000 : ℝ)+(87216606343/109287500000000 : ℝ)*((8919/50000 : ℝ)+(1819/20000 : ℝ))=(10000762028770177/10000000000000000 : ℝ) by norm_num, show 1+(16920134559836559/50000000000000000000 : ℝ)+(93144621870157/6250000000000000000 : ℝ)=(10003533058306959563/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16920134559836559/50000000000000000000 : ℝ) ≤ ((87417870378668569359/87430000000000000000 : ℝ)+2*(87216606343/109287500000000 : ℝ)*(8919/50000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (87417870378668569359/87430000000000000000 : ℝ)+2*(87216606343/109287500000000 : ℝ)*(8919/50000 : ℝ)=(10001459761620921/10000000000000000 : ℝ) by norm_num, show 1+2*(16920134559836559/50000000000000000000 : ℝ)=(25016920134559836559/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (87417870378668569359/87430000000000000000 : ℝ)*(X 1 0+X 2 0)+(87216606343/109287500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (1819/20000 : ℝ)) (hi := (8919/50000 : ℝ)) (c := (87417870378668569359/87430000000000000000 : ℝ)) (alpha := (87216606343/109287500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (87417870378668569359/87430000000000000000 : ℝ)*(X 0 1+X 2 1)+(87216606343/109287500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (1819/20000 : ℝ)) (hi := (8919/50000 : ℝ)) (c := (87417870378668569359/87430000000000000000 : ℝ)) (alpha := (87216606343/109287500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (87417870378668569359/87430000000000000000 : ℝ)*(X 0 2+X 1 2)+(87216606343/109287500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (1819/20000 : ℝ)) (hi := (8919/50000 : ℝ)) (c := (87417870378668569359/87430000000000000000 : ℝ)) (alpha := (87216606343/109287500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-853911869/5000000000 : ℝ)*X 0 0+(5467596233/10000000000 : ℝ)*X 0 1+(5174073119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071170019/2000000000 : ℝ)*X 1 0+(-1859422919/10000000000 : ℝ)*X 1 1+(5174072981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338962497/2500000000 : ℝ)*X 2 0+(5174073089/10000000000 : ℝ)*X 2 1+(-46485573/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((526649367/1250000000 : ℝ)*X 0 0+(966339493/2500000000 : ℝ)*X 0 1+(916949033/2000000000 : ℝ)*X 0 2+(526649367/1250000000 : ℝ)*X 1 0+(966339493/2500000000 : ℝ)*X 1 1+(916949033/2000000000 : ℝ)*X 1 2+(526649367/1250000000 : ℝ)*X 2 0+(966339493/2500000000 : ℝ)*X 2 1+(916949033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-426976299/2500000000 : ℝ)*X 0 0+(5176361419/10000000000 : ℝ)*X 0 1+(5465282923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638956831/5000000000 : ℝ)*X 1 0+(-784106559/5000000000 : ℝ)*X 1 1+(5465283041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638956953/5000000000 : ℝ)*X 2 0+(5465282541/10000000000 : ℝ)*X 2 1+(-1568213483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213395399/10000000000 : ℝ)*X 0 0+(4579137263/10000000000 : ℝ)*X 0 1+(1935513861/5000000000 : ℝ)*X 0 2+(4213395399/10000000000 : ℝ)*X 1 0+(4579137263/10000000000 : ℝ)*X 1 1+(1935513861/5000000000 : ℝ)*X 1 2+(4213395399/10000000000 : ℝ)*X 2 0+(4579137263/10000000000 : ℝ)*X 2 1+(1935513861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6284687092951879467175726467/546437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84614671/4000000000000 : ℝ)*(base19) + (495551907/25000000000000 : ℝ)*(base23) + (17431931/50000000000000 : ℝ)*(lower2) + (285492629/100000000000000 : ℝ)*(upper3) + (225371769/100000000000000 : ℝ)*(upper5) + (299814170673429/12500000000000 : ℝ)*(major0) + (299814170673429/12500000000000 : ℝ)*(major1) + (299814170673429/12500000000000 : ℝ)*(major2) + (851727775664463/25000000000000 : ℝ)*(sp0) + (851733156241251/25000000000000 : ℝ)*(sp1) + (68138655162483/2000000000000 : ℝ)*(sp2) + (1390081484857261/100000000000000 : ℝ)*(sp3) + (23637673927/100000000000000 : ℝ)*(sp4) + (10122212479/100000000000000 : ℝ)*(sp7) + (69504580353487/5000000000000 : ℝ)*(f.failure) + (1703467370165889/50000000000000 : ℝ)*(f.sum) + (165241440893873/43715000000000000000000000000 : ℝ)*base65 + (4811026137728212011/1092875000000000000000000000000000 : ℝ)*base67 + (3736492747059537989/1092875000000000000000000000000000 : ℝ)*base70 + (6533117144246087011/1092875000000000000000000000000000 : ℝ)*base71 + (11284714539587/43715000000000000000000000000 : ℝ)*base74 + (2757307254665162989/1092875000000000000000000000000000 : ℝ)*base76 + (6932087752838587011/1092875000000000000000000000000000 : ℝ)*base77 + (2485491500752837011/1092875000000000000000000000000000 : ℝ)*base79 + (180999673680237/43715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (798389/500000000000000000000 : ℝ)*base89 + (798389/500000000000000000000 : ℝ)*base91 + (798389/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2596390626815208835769126433/624500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293344011/100000000000000 : ℝ)*(base19) + (63813151/10000000000000 : ℝ)*(base23) + (56444697/100000000000000 : ℝ)*(upper3) + (27089199/25000000000000 : ℝ)*(lower4) + (8674071/25000000000000 : ℝ)*(upper5) + (2436678503709597/100000000000000 : ℝ)*(major0) + (2436678503709597/100000000000000 : ℝ)*(major1) + (2436678503709597/100000000000000 : ℝ)*(major2) + (2016071011/50000000000000 : ℝ)*(sp1) + (330273793/12500000000000 : ℝ)*(sp2) + (86528653194793/2500000000000 : ℝ)*(sp4) + (1730570901152843/50000000000000 : ℝ)*(sp5) + (692228569493973/20000000000000 : ℝ)*(sp6) + (5516448207197/390625000000 : ℝ)*(sp7) + (5516448207197/390625000000 : ℝ)*(f.failure) + (86528653194793/2500000000000 : ℝ)*(f.sum) + (5062353117033/780625000000000000000000000 : ℝ)*base65 + (8961544188646108811/1249000000000000000000000000000000 : ℝ)*base68 + (5242704354521891189/1249000000000000000000000000000000 : ℝ)*base69 + (13680264994147891189/1249000000000000000000000000000000 : ℝ)*base71 + (14646271140113/3122500000000000000000000000 : ℝ)*base74 + (5950560299330108811/1249000000000000000000000000000000 : ℝ)*base76 + (7705443253487891189/1249000000000000000000000000000000 : ℝ)*base77 + (2231333214004891189/1249000000000000000000000000000000 : ℝ)*base79 + (20352252716919/6245000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10183/19531250000000000000 : ℝ)*base90 + (10183/19531250000000000000 : ℝ)*base92 + (10183/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1608_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8919/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1819/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1608_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1608_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1608_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1608_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1608_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1608_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
