-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1537_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:17.100708+00:00
-- url     : https://prove2.me/submissions/65b840e4-7875-473a-957b-87e41e4c561f

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
theorem support_rectangle_w1537_s3_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-57229233/312500000 : ℝ)*x 0 + (5432460353/10000000000 : ℝ)*x 1 + (2608293907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57229233/312500000 : ℝ)^4571 ≤ (2243690357529/20000000000000 : ℝ)^3547 := by
    have hnat : (57229233 : ℕ)^4571*20000000000000^3547 ≤ 2243690357529^3547*312500000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57229233 312500000 2243690357529 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432460353/10000000000 : ℝ)^4571 ≤ (22775162812381/50000000000000 : ℝ)^3547 := by
    have hnat : (5432460353 : ℕ)^4571*50000000000000^3547 ≤ 22775162812381^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432460353 10000000000 22775162812381 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608293907/5000000000 : ℝ)^4571 ≤ (43231222570129/100000000000000 : ℝ)^3547 := by
    have hnat : (2608293907 : ℕ)^4571*100000000000000^3547 ≤ 43231222570129^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608293907 5000000000 43231222570129 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57229233/312500000 : ℝ), (5432460353/10000000000 : ℝ), (2608293907/5000000000 : ℝ)] ![(2243690357529/20000000000000 : ℝ), (22775162812381/50000000000000 : ℝ), (43231222570129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57229233/312500000 : ℝ)|^4571 ≤ (2243690357529/20000000000000 : ℝ)^3547
        have hw : |(-57229233/312500000 : ℝ)|=(57229233/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432460353/10000000000 : ℝ)|^4571 ≤ (22775162812381/50000000000000 : ℝ)^3547
        have hw : |(5432460353/10000000000 : ℝ)|=(5432460353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608293907/5000000000 : ℝ)|^4571 ≤ (43231222570129/100000000000000 : ℝ)^3547
        have hw : |(2608293907/5000000000 : ℝ)|=(2608293907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350813779/10000000000 : ℝ)*x 0 + (-1941897521/10000000000 : ℝ)*x 1 + (2608293831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350813779/10000000000 : ℝ)^4571 ≤ (4467001422107/10000000000000 : ℝ)^3547 := by
    have hnat : (5350813779 : ℕ)^4571*10000000000000^3547 ≤ 4467001422107^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350813779 10000000000 4467001422107 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941897521/10000000000 : ℝ)^4571 ≤ (24197529643/200000000000 : ℝ)^3547 := by
    have hnat : (1941897521 : ℕ)^4571*200000000000^3547 ≤ 24197529643^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941897521 10000000000 24197529643 200000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608293831/5000000000 : ℝ)^4571 ≤ (5403902618351/12500000000000 : ℝ)^3547 := by
    have hnat : (2608293831 : ℕ)^4571*12500000000000^3547 ≤ 5403902618351^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608293831 5000000000 5403902618351 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350813779/10000000000 : ℝ), (-1941897521/10000000000 : ℝ), (2608293831/5000000000 : ℝ)] ![(4467001422107/10000000000000 : ℝ), (24197529643/200000000000 : ℝ), (5403902618351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350813779/10000000000 : ℝ)|^4571 ≤ (4467001422107/10000000000000 : ℝ)^3547
        have hw : |(5350813779/10000000000 : ℝ)|=(5350813779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1941897521/10000000000 : ℝ)|^4571 ≤ (24197529643/200000000000 : ℝ)^3547
        have hw : |(-1941897521/10000000000 : ℝ)|=(1941897521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608293831/5000000000 : ℝ)|^4571 ≤ (5403902618351/12500000000000 : ℝ)^3547
        have hw : |(2608293831/5000000000 : ℝ)|=(2608293831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337703459/2500000000 : ℝ)*x 0 + (5216587487/10000000000 : ℝ)*x 1 + (-1941897677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337703459/2500000000 : ℝ)^4571 ≤ (44670014834297/100000000000000 : ℝ)^3547 := by
    have hnat : (1337703459 : ℕ)^4571*100000000000000^3547 ≤ 44670014834297^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337703459 2500000000 44670014834297 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216587487/10000000000 : ℝ)^4571 ≤ (10807804769463/25000000000000 : ℝ)^3547 := by
    have hnat : (5216587487 : ℕ)^4571*25000000000000^3547 ≤ 10807804769463^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216587487 10000000000 10807804769463 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941897677/10000000000 : ℝ)^4571 ≤ (12098766074033/100000000000000 : ℝ)^3547 := by
    have hnat : (1941897677 : ℕ)^4571*100000000000000^3547 ≤ 12098766074033^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941897677 10000000000 12098766074033 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337703459/2500000000 : ℝ), (5216587487/10000000000 : ℝ), (-1941897677/10000000000 : ℝ)] ![(44670014834297/100000000000000 : ℝ), (10807804769463/25000000000000 : ℝ), (12098766074033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337703459/2500000000 : ℝ)|^4571 ≤ (44670014834297/100000000000000 : ℝ)^3547
        have hw : |(1337703459/2500000000 : ℝ)|=(1337703459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216587487/10000000000 : ℝ)|^4571 ≤ (10807804769463/25000000000000 : ℝ)^3547
        have hw : |(5216587487/10000000000 : ℝ)|=(5216587487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1941897677/10000000000 : ℝ)|^4571 ≤ (12098766074033/100000000000000 : ℝ)^3547
        have hw : |(-1941897677/10000000000 : ℝ)|=(1941897677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851607381/2000000000 : ℝ)*x 0 + (200751157/500000000 : ℝ)*x 1 + (2256584113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851607381/2000000000 : ℝ)^4571 ≤ (3327853174211/10000000000000 : ℝ)^3547 := by
    have hnat : (851607381 : ℕ)^4571*10000000000000^3547 ≤ 3327853174211^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851607381 2000000000 3327853174211 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200751157/500000000 : ℝ)^4571 ≤ (30851402027847/100000000000000 : ℝ)^3547 := by
    have hnat : (200751157 : ℕ)^4571*100000000000000^3547 ≤ 30851402027847^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200751157 500000000 30851402027847 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256584113/5000000000 : ℝ)^4571 ≤ (8967516553923/25000000000000 : ℝ)^3547 := by
    have hnat : (2256584113 : ℕ)^4571*25000000000000^3547 ≤ 8967516553923^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256584113 5000000000 8967516553923 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851607381/2000000000 : ℝ), (200751157/500000000 : ℝ), (2256584113/5000000000 : ℝ)] ![(3327853174211/10000000000000 : ℝ), (30851402027847/100000000000000 : ℝ), (8967516553923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851607381/2000000000 : ℝ)|^4571 ≤ (3327853174211/10000000000000 : ℝ)^3547
        have hw : |(851607381/2000000000 : ℝ)|=(851607381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200751157/500000000 : ℝ)|^4571 ≤ (30851402027847/100000000000000 : ℝ)^3547
        have hw : |(200751157/500000000 : ℝ)|=(200751157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2256584113/5000000000 : ℝ)|^4571 ≤ (8967516553923/25000000000000 : ℝ)^3547
        have hw : |(2256584113/5000000000 : ℝ)|=(2256584113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1831365757/10000000000 : ℝ)*x 0 + (52177289/100000000 : ℝ)*x 1 + (5431310339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831365757/10000000000 : ℝ)^4571 ≤ (2804672748547/25000000000000 : ℝ)^3547 := by
    have hnat : (1831365757 : ℕ)^4571*25000000000000^3547 ≤ 2804672748547^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831365757 10000000000 2804672748547 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52177289/100000000 : ℝ)^4571 ≤ (5405426183307/12500000000000 : ℝ)^3547 := by
    have hnat : (52177289 : ℕ)^4571*12500000000000^3547 ≤ 5405426183307^3547*100000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52177289 100000000 5405426183307 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431310339/10000000000 : ℝ)^4571 ≤ (22768949762887/50000000000000 : ℝ)^3547 := by
    have hnat : (5431310339 : ℕ)^4571*50000000000000^3547 ≤ 22768949762887^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431310339 10000000000 22768949762887 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1831365757/10000000000 : ℝ), (52177289/100000000 : ℝ), (5431310339/10000000000 : ℝ)] ![(2804672748547/25000000000000 : ℝ), (5405426183307/12500000000000 : ℝ), (22768949762887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1831365757/10000000000 : ℝ)|^4571 ≤ (2804672748547/25000000000000 : ℝ)^3547
        have hw : |(-1831365757/10000000000 : ℝ)|=(1831365757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52177289/100000000 : ℝ)|^4571 ≤ (5405426183307/12500000000000 : ℝ)^3547
        have hw : |(52177289/100000000 : ℝ)|=(52177289/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431310339/10000000000 : ℝ)|^4571 ≤ (22768949762887/50000000000000 : ℝ)^3547
        have hw : |(5431310339/10000000000 : ℝ)|=(5431310339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646969803/5000000000 : ℝ)*x 0 + (-1727174897/10000000000 : ℝ)*x 1 + (54313103/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646969803/5000000000 : ℝ)^4571 ≤ (22029541125873/50000000000000 : ℝ)^3547 := by
    have hnat : (2646969803 : ℕ)^4571*50000000000000^3547 ≤ 22029541125873^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646969803 5000000000 22029541125873 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1727174897/10000000000 : ℝ)^4571 ≤ (10403018621649/100000000000000 : ℝ)^3547 := by
    have hnat : (1727174897 : ℕ)^4571*100000000000000^3547 ≤ 10403018621649^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727174897 10000000000 10403018621649 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54313103/100000000 : ℝ)^4571 ≤ (9107579820877/20000000000000 : ℝ)^3547 := by
    have hnat : (54313103 : ℕ)^4571*20000000000000^3547 ≤ 9107579820877^3547*100000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54313103 100000000 9107579820877 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646969803/5000000000 : ℝ), (-1727174897/10000000000 : ℝ), (54313103/100000000 : ℝ)] ![(22029541125873/50000000000000 : ℝ), (10403018621649/100000000000000 : ℝ), (9107579820877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646969803/5000000000 : ℝ)|^4571 ≤ (22029541125873/50000000000000 : ℝ)^3547
        have hw : |(2646969803/5000000000 : ℝ)|=(2646969803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1727174897/10000000000 : ℝ)|^4571 ≤ (10403018621649/100000000000000 : ℝ)^3547
        have hw : |(-1727174897/10000000000 : ℝ)|=(1727174897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54313103/100000000 : ℝ)|^4571 ≤ (9107579820877/20000000000000 : ℝ)^3547
        have hw : |(54313103/100000000 : ℝ)|=(54313103/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058787919/2000000000 : ℝ)*x 0 + (5431310311/10000000000 : ℝ)*x 1 + (-863587449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058787919/2000000000 : ℝ)^4571 ≤ (44059082133769/100000000000000 : ℝ)^3547 := by
    have hnat : (1058787919 : ℕ)^4571*100000000000000^3547 ≤ 44059082133769^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058787919 2000000000 44059082133769 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431310311/10000000000 : ℝ)^4571 ≤ (22768949611619/50000000000000 : ℝ)^3547 := by
    have hnat : (5431310311 : ℕ)^4571*50000000000000^3547 ≤ 22768949611619^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431310311 10000000000 22768949611619 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863587449/5000000000 : ℝ)^4571 ≤ (10403018629411/100000000000000 : ℝ)^3547 := by
    have hnat : (863587449 : ℕ)^4571*100000000000000^3547 ≤ 10403018629411^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863587449 5000000000 10403018629411 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058787919/2000000000 : ℝ), (5431310311/10000000000 : ℝ), (-863587449/5000000000 : ℝ)] ![(44059082133769/100000000000000 : ℝ), (22768949611619/50000000000000 : ℝ), (10403018629411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058787919/2000000000 : ℝ)|^4571 ≤ (44059082133769/100000000000000 : ℝ)^3547
        have hw : |(1058787919/2000000000 : ℝ)|=(1058787919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431310311/10000000000 : ℝ)|^4571 ≤ (22768949611619/50000000000000 : ℝ)^3547
        have hw : |(5431310311/10000000000 : ℝ)|=(5431310311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-863587449/5000000000 : ℝ)|^4571 ≤ (10403018629411/100000000000000 : ℝ)^3547
        have hw : |(-863587449/5000000000 : ℝ)|=(863587449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s3_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851621223/2000000000 : ℝ)*x 0 + (2255267233/5000000000 : ℝ)*x 1 + (401767647/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851621223/2000000000 : ℝ)^4571 ≤ (8319807202323/25000000000000 : ℝ)^3547 := by
    have hnat : (851621223 : ℕ)^4571*25000000000000^3547 ≤ 8319807202323^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851621223 2000000000 8319807202323 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255267233/5000000000 : ℝ)^4571 ≤ (35843092529757/100000000000000 : ℝ)^3547 := by
    have hnat : (2255267233 : ℕ)^4571*100000000000000^3547 ≤ 35843092529757^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255267233 5000000000 35843092529757 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401767647/1000000000 : ℝ)^4571 ≤ (15438839326101/50000000000000 : ℝ)^3547 := by
    have hnat : (401767647 : ℕ)^4571*50000000000000^3547 ≤ 15438839326101^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401767647 1000000000 15438839326101 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851621223/2000000000 : ℝ), (2255267233/5000000000 : ℝ), (401767647/1000000000 : ℝ)] ![(8319807202323/25000000000000 : ℝ), (35843092529757/100000000000000 : ℝ), (15438839326101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851621223/2000000000 : ℝ)|^4571 ≤ (8319807202323/25000000000000 : ℝ)^3547
        have hw : |(851621223/2000000000 : ℝ)|=(851621223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255267233/5000000000 : ℝ)|^4571 ≤ (35843092529757/100000000000000 : ℝ)^3547
        have hw : |(2255267233/5000000000 : ℝ)|=(2255267233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401767647/1000000000 : ℝ)|^4571 ≤ (15438839326101/50000000000000 : ℝ)^3547
        have hw : |(401767647/1000000000 : ℝ)|=(401767647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5481/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (971/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5309/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5309/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5309/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5309/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5309/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5309/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5309/50000 : ℝ) ^ (4569/1024 : ℝ) ≤ (4511140158441777/100000000000000000000 : ℝ) := by
    have hpowers : (5309/50000 : ℝ)^4569 ≤ (4511140158441777/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5309 : ℕ)^4569*100000000000000000000^1024 ≤ 4511140158441777^1024*50000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5309 50000 4511140158441777 100000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5309/50000 : ℝ)) (X := (4511140158441777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15909/100000 : ℝ) ^ (4569/1024 : ℝ) ≤ (3425383178019687/12500000000000000000 : ℝ) := by
    have hpowers : (15909/100000 : ℝ)^4569 ≤ (3425383178019687/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15909 : ℕ)^4569*12500000000000000000^1024 ≤ 3425383178019687^1024*100000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15909 100000 3425383178019687 12500000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15909/100000 : ℝ)) (X := (3425383178019687/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004511140158441777/50000000000000000000 : ℝ) ≤ (2000040439884847/2000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (50004511140158441777/50000000000000000000 : ℝ)^1024 ≤ (2000040439884847/2000000000000000 : ℝ)^4569 := by
      have hnat : (50004511140158441777 : ℕ)^1024*2000000000000000^4569 ≤ 2000040439884847^4569*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004511140158441777 50000000000000000000 2000040439884847 2000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000040439884847/2000000000000000 : ℝ)) (X := (50004511140158441777/50000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031914205582599273/100000000000000000000 : ℝ) ≤ (5000357584823959/5000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (100031914205582599273/100000000000000000000 : ℝ)^1024 ≤ (5000357584823959/5000000000000000 : ℝ)^4569 := by
      have hnat : (100031914205582599273 : ℕ)^1024*5000000000000000^4569 ≤ 5000357584823959^4569*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031914205582599273 100000000000000000000 5000357584823959 5000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357584823959/5000000000000000 : ℝ)) (X := (100031914205582599273/100000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253425383178019687/6250000000000000000 : ℝ) ≤ (10001228139871601/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (6253425383178019687/6250000000000000000 : ℝ)^1024 ≤ (10001228139871601/10000000000000000 : ℝ)^4569 := by
      have hnat : (6253425383178019687 : ℕ)^1024*10000000000000000^4569 ≤ 10001228139871601^4569*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253425383178019687 6250000000000000000 10001228139871601 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228139871601/10000000000000000 : ℝ)) (X := (6253425383178019687/6250000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4511140158441777/100000000000000000000 : ℝ) ≤ ((52900176401483495197/52910000000000000000 : ℝ)+2*(512970223683/529100000000000 : ℝ)*(5309/50000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (52900176401483495197/52910000000000000000 : ℝ)+2*(512970223683/529100000000000 : ℝ)*(5309/50000 : ℝ)=(2000040439884847/2000000000000000 : ℝ) by norm_num, show 1+2*(4511140158441777/100000000000000000000 : ℝ)=(50004511140158441777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3425383178019687/12500000000000000000 : ℝ)+(4511140158441777/100000000000000000000 : ℝ) ≤ ((52900176401483495197/52910000000000000000 : ℝ)+(512970223683/529100000000000 : ℝ)*((15909/100000 : ℝ)+(5309/50000 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (52900176401483495197/52910000000000000000 : ℝ)+(512970223683/529100000000000 : ℝ)*((15909/100000 : ℝ)+(5309/50000 : ℝ))=(5000357584823959/5000000000000000 : ℝ) by norm_num, show 1+(3425383178019687/12500000000000000000 : ℝ)+(4511140158441777/100000000000000000000 : ℝ)=(100031914205582599273/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3425383178019687/12500000000000000000 : ℝ) ≤ ((52900176401483495197/52910000000000000000 : ℝ)+2*(512970223683/529100000000000 : ℝ)*(15909/100000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (52900176401483495197/52910000000000000000 : ℝ)+2*(512970223683/529100000000000 : ℝ)*(15909/100000 : ℝ)=(10001228139871601/10000000000000000 : ℝ) by norm_num, show 1+2*(3425383178019687/12500000000000000000 : ℝ)=(6253425383178019687/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52900176401483495197/52910000000000000000 : ℝ)*(X 1 0+X 2 0)+(512970223683/529100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (5309/50000 : ℝ)) (hi := (15909/100000 : ℝ)) (c := (52900176401483495197/52910000000000000000 : ℝ)) (alpha := (512970223683/529100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52900176401483495197/52910000000000000000 : ℝ)*(X 0 1+X 2 1)+(512970223683/529100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (5309/50000 : ℝ)) (hi := (15909/100000 : ℝ)) (c := (52900176401483495197/52910000000000000000 : ℝ)) (alpha := (512970223683/529100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52900176401483495197/52910000000000000000 : ℝ)*(X 0 2+X 1 2)+(512970223683/529100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (5309/50000 : ℝ)) (hi := (15909/100000 : ℝ)) (c := (52900176401483495197/52910000000000000000 : ℝ)) (alpha := (512970223683/529100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-57229233/312500000 : ℝ)*X 0 0+(5432460353/10000000000 : ℝ)*X 0 1+(2608293907/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350813779/10000000000 : ℝ)*X 1 0+(-1941897521/10000000000 : ℝ)*X 1 1+(2608293831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337703459/2500000000 : ℝ)*X 2 0+(5216587487/10000000000 : ℝ)*X 2 1+(-1941897677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((851607381/2000000000 : ℝ)*X 0 0+(200751157/500000000 : ℝ)*X 0 1+(2256584113/5000000000 : ℝ)*X 0 2+(851607381/2000000000 : ℝ)*X 1 0+(200751157/500000000 : ℝ)*X 1 1+(2256584113/5000000000 : ℝ)*X 1 2+(851607381/2000000000 : ℝ)*X 2 0+(200751157/500000000 : ℝ)*X 2 1+(2256584113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1831365757/10000000000 : ℝ)*X 0 0+(52177289/100000000 : ℝ)*X 0 1+(5431310339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646969803/5000000000 : ℝ)*X 1 0+(-1727174897/10000000000 : ℝ)*X 1 1+(54313103/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058787919/2000000000 : ℝ)*X 2 0+(5431310311/10000000000 : ℝ)*X 2 1+(-863587449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851621223/2000000000 : ℝ)*X 0 0+(2255267233/5000000000 : ℝ)*X 0 1+(401767647/1000000000 : ℝ)*X 0 2+(851621223/2000000000 : ℝ)*X 1 0+(2255267233/5000000000 : ℝ)*X 1 1+(401767647/1000000000 : ℝ)*X 1 2+(851621223/2000000000 : ℝ)*X 2 0+(2255267233/5000000000 : ℝ)*X 2 1+(401767647/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80678584551283170153687/26455000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86147553/50000000000000 : ℝ)*(base23) + (43253111/100000000000000 : ℝ)*(lower2) + (8801491/12500000000000 : ℝ)*(lower3) + (59008843/50000000000000 : ℝ)*(lower4) + (5670461/12500000000000 : ℝ)*(lower5) + (829976459251941/25000000000000 : ℝ)*(major0) + (829976459251941/25000000000000 : ℝ)*(major1) + (829976459251941/25000000000000 : ℝ)*(major2) + (1158090911618137/25000000000000 : ℝ)*(sp0) + (1158090911618137/25000000000000 : ℝ)*(sp1) + (2316180947878719/50000000000000 : ℝ)*(sp2) + (1003723952826401/50000000000000 : ℝ)*(sp3) + (315684001/20000000000000 : ℝ)*(sp6) + (4047011/20000000000000 : ℝ)*(sp7) + (2007447925887857/100000000000000 : ℝ)*(f.failure) + (1158090911618137/25000000000000 : ℝ)*(f.sum) + (119682581205427/26455000000000000000000000000 : ℝ)*base65 + (4970653843553227377/1322750000000000000000000000000000 : ℝ)*base67 + (401052831148227377/1322750000000000000000000000000000 : ℝ)*base69 + (2998004132342477377/1322750000000000000000000000000000 : ℝ)*base71 + (363398294951/13227500000000000000000000000 : ℝ)*base73 + (7186469613067772623/1322750000000000000000000000000000 : ℝ)*base76 + (5436208664917772623/1322750000000000000000000000000000 : ℝ)*base78 + (11418563123033522623/1322750000000000000000000000000000 : ℝ)*base80 + (112886715877341/13227500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (205689/400000000000000000000 : ℝ)*base89 + (205689/400000000000000000000 : ℝ)*base91 + (205689/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6776436209554608083601888711/661375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860745879/50000000000000 : ℝ)*(base19) + (230710157/12500000000000 : ℝ)*(base23) + (6671729/3125000000000 : ℝ)*(upper3) + (31109777/50000000000000 : ℝ)*(lower4) + (2828553/1250000000000 : ℝ)*(upper5) + (838879483145679/25000000000000 : ℝ)*(major0) + (838879483145679/25000000000000 : ℝ)*(major1) + (838879483145679/25000000000000 : ℝ)*(major2) + (12917613911/50000000000000 : ℝ)*(sp1) + (27360645763/100000000000000 : ℝ)*(sp2) + (4682054026942459/100000000000000 : ℝ)*(sp4) + (29262665438893/625000000000 : ℝ)*(sp5) + (58525310257693/1250000000000 : ℝ)*(sp6) + (1014490748345121/50000000000000 : ℝ)*(sp7) + (1014490748345121/50000000000000 : ℝ)*(f.failure) + (4682054026942459/100000000000000 : ℝ)*(f.sum) + (115275962839043/26455000000000000000000000000 : ℝ)*base65 + (3790613121635503763/1322750000000000000000000000000000 : ℝ)*base67 + (1758248351984246237/1322750000000000000000000000000000 : ℝ)*base70 + (6106578297731503763/1322750000000000000000000000000000 : ℝ)*base71 + (24699962472611/13227500000000000000000000000 : ℝ)*base74 + (15672536769692496237/1322750000000000000000000000000000 : ℝ)*base76 + (2140472409344003763/1322750000000000000000000000000000 : ℝ)*base77 + (2227381456032753763/1322750000000000000000000000000000 : ℝ)*base79 + (62521129297633/26455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (501417/200000000000000000000 : ℝ)*base89 + (501417/200000000000000000000 : ℝ)*base91 + (501417/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1537_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (971/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1537_s4_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1831664383/10000000000 : ℝ)*x 0 + (1086054857/2000000000 : ℝ)*x 1 + (5218556243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831664383/10000000000 : ℝ)^4571 ≤ (11221048511921/100000000000000 : ℝ)^3547 := by
    have hnat : (1831664383 : ℕ)^4571*100000000000000^3547 ≤ 11221048511921^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831664383 10000000000 11221048511921 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086054857/2000000000 : ℝ)^4571 ≤ (45526705434557/100000000000000 : ℝ)^3547 := by
    have hnat : (1086054857 : ℕ)^4571*100000000000000^3547 ≤ 45526705434557^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086054857 2000000000 45526705434557 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218556243/10000000000 : ℝ)^4571 ≤ (21626123020921/50000000000000 : ℝ)^3547 := by
    have hnat : (5218556243 : ℕ)^4571*50000000000000^3547 ≤ 21626123020921^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218556243 10000000000 21626123020921 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1831664383/10000000000 : ℝ), (1086054857/2000000000 : ℝ), (5218556243/10000000000 : ℝ)] ![(11221048511921/100000000000000 : ℝ), (45526705434557/100000000000000 : ℝ), (21626123020921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1831664383/10000000000 : ℝ)|^4571 ≤ (11221048511921/100000000000000 : ℝ)^3547
        have hw : |(-1831664383/10000000000 : ℝ)|=(1831664383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086054857/2000000000 : ℝ)|^4571 ≤ (45526705434557/100000000000000 : ℝ)^3547
        have hw : |(1086054857/2000000000 : ℝ)|=(1086054857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218556243/10000000000 : ℝ)|^4571 ≤ (21626123020921/50000000000000 : ℝ)^3547
        have hw : |(5218556243/10000000000 : ℝ)|=(5218556243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350239169/10000000000 : ℝ)*x 0 + (-1940048721/10000000000 : ℝ)*x 1 + (2609278063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350239169/10000000000 : ℝ)^4571 ≤ (44663832452611/100000000000000 : ℝ)^3547 := by
    have hnat : (5350239169 : ℕ)^4571*100000000000000^3547 ≤ 44663832452611^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350239169 10000000000 44663832452611 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940048721/10000000000 : ℝ)^4571 ≤ (3020980683467/25000000000000 : ℝ)^3547 := by
    have hnat : (1940048721 : ℕ)^4571*25000000000000^3547 ≤ 3020980683467^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940048721 10000000000 3020980683467 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609278063/5000000000 : ℝ)^4571 ≤ (1730089791687/4000000000000 : ℝ)^3547 := by
    have hnat : (2609278063 : ℕ)^4571*4000000000000^3547 ≤ 1730089791687^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609278063 5000000000 1730089791687 4000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350239169/10000000000 : ℝ), (-1940048721/10000000000 : ℝ), (2609278063/5000000000 : ℝ)] ![(44663832452611/100000000000000 : ℝ), (3020980683467/25000000000000 : ℝ), (1730089791687/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350239169/10000000000 : ℝ)|^4571 ≤ (44663832452611/100000000000000 : ℝ)^3547
        have hw : |(5350239169/10000000000 : ℝ)|=(5350239169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1940048721/10000000000 : ℝ)|^4571 ≤ (3020980683467/25000000000000 : ℝ)^3547
        have hw : |(-1940048721/10000000000 : ℝ)|=(1940048721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609278063/5000000000 : ℝ)|^4571 ≤ (1730089791687/4000000000000 : ℝ)^3547
        have hw : |(2609278063/5000000000 : ℝ)|=(2609278063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535023887/1000000000 : ℝ)*x 0 + (1304639123/2500000000 : ℝ)*x 1 + (-485012159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535023887/1000000000 : ℝ)^4571 ≤ (1116595730899/2500000000000 : ℝ)^3547 := by
    have hnat : (535023887 : ℕ)^4571*2500000000000^3547 ≤ 1116595730899^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535023887 1000000000 1116595730899 2500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304639123/2500000000 : ℝ)^4571 ≤ (43252248701389/100000000000000 : ℝ)^3547 := by
    have hnat : (1304639123 : ℕ)^4571*100000000000000^3547 ≤ 43252248701389^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304639123 2500000000 43252248701389 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485012159/2500000000 : ℝ)^4571 ≤ (6041961025793/50000000000000 : ℝ)^3547 := by
    have hnat : (485012159 : ℕ)^4571*50000000000000^3547 ≤ 6041961025793^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485012159 2500000000 6041961025793 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535023887/1000000000 : ℝ), (1304639123/2500000000 : ℝ), (-485012159/2500000000 : ℝ)] ![(1116595730899/2500000000000 : ℝ), (43252248701389/100000000000000 : ℝ), (6041961025793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535023887/1000000000 : ℝ)|^4571 ≤ (1116595730899/2500000000000 : ℝ)^3547
        have hw : |(535023887/1000000000 : ℝ)|=(535023887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304639123/2500000000 : ℝ)|^4571 ≤ (43252248701389/100000000000000 : ℝ)^3547
        have hw : |(1304639123/2500000000 : ℝ)|=(1304639123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485012159/2500000000 : ℝ)|^4571 ≤ (6041961025793/50000000000000 : ℝ)^3547
        have hw : |(-485012159/2500000000 : ℝ)|=(485012159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064560989/2500000000 : ℝ)*x 0 + (2009896869/5000000000 : ℝ)*x 1 + (28177193/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064560989/2500000000 : ℝ)^4571 ≤ (16640308560923/50000000000000 : ℝ)^3547 := by
    have hnat : (1064560989 : ℕ)^4571*50000000000000^3547 ≤ 16640308560923^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064560989 2500000000 16640308560923 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009896869/5000000000 : ℝ)^4571 ≤ (3862331263499/12500000000000 : ℝ)^3547 := by
    have hnat : (2009896869 : ℕ)^4571*12500000000000^3547 ≤ 3862331263499^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009896869 5000000000 3862331263499 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28177193/62500000 : ℝ)^4571 ≤ (35820732753743/100000000000000 : ℝ)^3547 := by
    have hnat : (28177193 : ℕ)^4571*100000000000000^3547 ≤ 35820732753743^3547*62500000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28177193 62500000 35820732753743 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064560989/2500000000 : ℝ), (2009896869/5000000000 : ℝ), (28177193/62500000 : ℝ)] ![(16640308560923/50000000000000 : ℝ), (3862331263499/12500000000000 : ℝ), (35820732753743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064560989/2500000000 : ℝ)|^4571 ≤ (16640308560923/50000000000000 : ℝ)^3547
        have hw : |(1064560989/2500000000 : ℝ)|=(1064560989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009896869/5000000000 : ℝ)|^4571 ≤ (3862331263499/12500000000000 : ℝ)^3547
        have hw : |(2009896869/5000000000 : ℝ)|=(2009896869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28177193/62500000 : ℝ)|^4571 ≤ (35820732753743/100000000000000 : ℝ)^3547
        have hw : |(28177193/62500000 : ℝ)|=(28177193/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-114480793/625000000 : ℝ)*x 0 + (5219654293/10000000000 : ℝ)*x 1 + (5429168021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114480793/625000000 : ℝ)^4571 ≤ (11221271972901/100000000000000 : ℝ)^3547 := by
    have hnat : (114480793 : ℕ)^4571*100000000000000^3547 ≤ 11221271972901^3547*625000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114480793 625000000 11221271972901 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219654293/10000000000 : ℝ)^4571 ≤ (43263974573251/100000000000000 : ℝ)^3547 := by
    have hnat : (5219654293 : ℕ)^4571*100000000000000^3547 ≤ 43263974573251^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219654293 10000000000 43263974573251 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429168021/10000000000 : ℝ)^4571 ≤ (22757376718473/50000000000000 : ℝ)^3547 := by
    have hnat : (5429168021 : ℕ)^4571*50000000000000^3547 ≤ 22757376718473^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429168021 10000000000 22757376718473 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114480793/625000000 : ℝ), (5219654293/10000000000 : ℝ), (5429168021/10000000000 : ℝ)] ![(11221271972901/100000000000000 : ℝ), (43263974573251/100000000000000 : ℝ), (22757376718473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114480793/625000000 : ℝ)|^4571 ≤ (11221271972901/100000000000000 : ℝ)^3547
        have hw : |(-114480793/625000000 : ℝ)|=(114480793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219654293/10000000000 : ℝ)|^4571 ≤ (43263974573251/100000000000000 : ℝ)^3547
        have hw : |(5219654293/10000000000 : ℝ)|=(5219654293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429168021/10000000000 : ℝ)|^4571 ≤ (22757376718473/50000000000000 : ℝ)^3547
        have hw : |(5429168021/10000000000 : ℝ)|=(5429168021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294460101/10000000000 : ℝ)*x 0 + (-864718613/5000000000 : ℝ)*x 1 + (5429167991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294460101/10000000000 : ℝ)^4571 ≤ (44064664758051/100000000000000 : ℝ)^3547 := by
    have hnat : (5294460101 : ℕ)^4571*100000000000000^3547 ≤ 44064664758051^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294460101 10000000000 44064664758051 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864718613/5000000000 : ℝ)^4571 ≤ (2084116423269/20000000000000 : ℝ)^3547 := by
    have hnat : (864718613 : ℕ)^4571*20000000000000^3547 ≤ 2084116423269^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864718613 5000000000 2084116423269 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429167991/10000000000 : ℝ)^4571 ≤ (22757376556419/50000000000000 : ℝ)^3547 := by
    have hnat : (5429167991 : ℕ)^4571*50000000000000^3547 ≤ 22757376556419^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429167991 10000000000 22757376556419 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294460101/10000000000 : ℝ), (-864718613/5000000000 : ℝ), (5429167991/10000000000 : ℝ)] ![(44064664758051/100000000000000 : ℝ), (2084116423269/20000000000000 : ℝ), (22757376556419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294460101/10000000000 : ℝ)|^4571 ≤ (44064664758051/100000000000000 : ℝ)^3547
        have hw : |(5294460101/10000000000 : ℝ)|=(5294460101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-864718613/5000000000 : ℝ)|^4571 ≤ (2084116423269/20000000000000 : ℝ)^3547
        have hw : |(-864718613/5000000000 : ℝ)|=(864718613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429167991/10000000000 : ℝ)|^4571 ≤ (22757376556419/50000000000000 : ℝ)^3547
        have hw : |(5429167991/10000000000 : ℝ)|=(5429167991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294460151/10000000000 : ℝ)*x 0 + (2714583993/5000000000 : ℝ)*x 1 + (-1729437163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294460151/10000000000 : ℝ)^4571 ≤ (44064665294327/100000000000000 : ℝ)^3547 := by
    have hnat : (5294460151 : ℕ)^4571*100000000000000^3547 ≤ 44064665294327^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294460151 10000000000 44064665294327 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714583993/5000000000 : ℝ)^4571 ≤ (2275737652941/5000000000000 : ℝ)^3547 := by
    have hnat : (2714583993 : ℕ)^4571*5000000000000^3547 ≤ 2275737652941^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714583993 5000000000 2275737652941 5000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1729437163/10000000000 : ℝ)^4571 ≤ (2084116325431/20000000000000 : ℝ)^3547 := by
    have hnat : (1729437163 : ℕ)^4571*20000000000000^3547 ≤ 2084116325431^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729437163 10000000000 2084116325431 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294460151/10000000000 : ℝ), (2714583993/5000000000 : ℝ), (-1729437163/10000000000 : ℝ)] ![(44064665294327/100000000000000 : ℝ), (2275737652941/5000000000000 : ℝ), (2084116325431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294460151/10000000000 : ℝ)|^4571 ≤ (44064665294327/100000000000000 : ℝ)^3547
        have hw : |(5294460151/10000000000 : ℝ)|=(5294460151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714583993/5000000000 : ℝ)|^4571 ≤ (2275737652941/5000000000000 : ℝ)^3547
        have hw : |(2714583993/5000000000 : ℝ)|=(2714583993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1729437163/10000000000 : ℝ)|^4571 ≤ (2084116325431/20000000000000 : ℝ)^3547
        have hw : |(-1729437163/10000000000 : ℝ)|=(1729437163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s4_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129154739/5000000000 : ℝ)*x 0 + (1126454281/2500000000 : ℝ)*x 1 + (4022345733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129154739/5000000000 : ℝ)^4571 ≤ (16640638526761/50000000000000 : ℝ)^3547 := by
    have hnat : (2129154739 : ℕ)^4571*50000000000000^3547 ≤ 16640638526761^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129154739 5000000000 16640638526761 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126454281/2500000000 : ℝ)^4571 ≤ (4474348897337/12500000000000 : ℝ)^3547 := by
    have hnat : (1126454281 : ℕ)^4571*12500000000000^3547 ≤ 4474348897337^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126454281 2500000000 4474348897337 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022345733/10000000000 : ℝ)^4571 ≤ (30923931755979/100000000000000 : ℝ)^3547 := by
    have hnat : (4022345733 : ℕ)^4571*100000000000000^3547 ≤ 30923931755979^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022345733 10000000000 30923931755979 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129154739/5000000000 : ℝ), (1126454281/2500000000 : ℝ), (4022345733/10000000000 : ℝ)] ![(16640638526761/50000000000000 : ℝ), (4474348897337/12500000000000 : ℝ), (30923931755979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129154739/5000000000 : ℝ)|^4571 ≤ (16640638526761/50000000000000 : ℝ)^3547
        have hw : |(2129154739/5000000000 : ℝ)|=(2129154739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126454281/2500000000 : ℝ)|^4571 ≤ (4474348897337/12500000000000 : ℝ)^3547
        have hw : |(1126454281/2500000000 : ℝ)|=(1126454281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022345733/10000000000 : ℝ)|^4571 ≤ (30923931755979/100000000000000 : ℝ)^3547
        have hw : |(4022345733/10000000000 : ℝ)|=(4022345733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (971/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2751/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (971/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (971/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5481/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (971/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (971/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5481/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (971/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (971/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5481/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5481/50000 : ℝ) ^ (4569/1024 : ℝ) ≤ (40631309309317/781250000000000000 : ℝ) := by
    have hpowers : (5481/50000 : ℝ)^4569 ≤ (40631309309317/781250000000000000 : ℝ)^1024 := by
      have hnat : (5481 : ℕ)^4569*781250000000000000^1024 ≤ 40631309309317^1024*50000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5481 50000 40631309309317 781250000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5481/50000 : ℝ)) (X := (40631309309317/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (971/6250 : ℝ) ^ (4569/1024 : ℝ) ≤ (24650461857625161/100000000000000000000 : ℝ) := by
    have hpowers : (971/6250 : ℝ)^4569 ≤ (24650461857625161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (971 : ℕ)^4569*100000000000000000000^1024 ≤ 24650461857625161^1024*6250^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        971 6250 24650461857625161 100000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (971/6250 : ℝ)) (X := (24650461857625161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (390665631309309317/390625000000000000 : ℝ) ≤ (500011655530941/500000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (390665631309309317/390625000000000000 : ℝ)^1024 ≤ (500011655530941/500000000000000 : ℝ)^4569 := by
      have hnat : (390665631309309317 : ℕ)^1024*500000000000000^4569 ≤ 500011655530941^4569*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390665631309309317 390625000000000000 500011655530941 500000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500011655530941/500000000000000 : ℝ)) (X := (390665631309309317/390625000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029851269449217737/100000000000000000000 : ℝ) ≤ (10000668946391863/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (100029851269449217737/100000000000000000000 : ℝ)^1024 ≤ (10000668946391863/10000000000000000 : ℝ)^4569 := by
      have hnat : (100029851269449217737 : ℕ)^1024*10000000000000000^4569 ≤ 10000668946391863^4569*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029851269449217737 100000000000000000000 10000668946391863 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668946391863/10000000000000000 : ℝ)) (X := (100029851269449217737/100000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024650461857625161/50000000000000000000 : ℝ) ≤ (5000552391082453/5000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (50024650461857625161/50000000000000000000 : ℝ)^1024 ≤ (5000552391082453/5000000000000000 : ℝ)^4569 := by
      have hnat : (50024650461857625161 : ℕ)^1024*5000000000000000^4569 ≤ 5000552391082453^4569*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024650461857625161 50000000000000000000 5000552391082453 5000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000552391082453/5000000000000000 : ℝ)) (X := (50024650461857625161/50000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(40631309309317/781250000000000000 : ℝ) ≤ ((11432877746120571987/11435000000000000000 : ℝ)+2*(435835773043/457400000000000 : ℝ)*(5481/50000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (11432877746120571987/11435000000000000000 : ℝ)+2*(435835773043/457400000000000 : ℝ)*(5481/50000 : ℝ)=(500011655530941/500000000000000 : ℝ) by norm_num, show 1+2*(40631309309317/781250000000000000 : ℝ)=(390665631309309317/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24650461857625161/100000000000000000000 : ℝ)+(40631309309317/781250000000000000 : ℝ) ≤ ((11432877746120571987/11435000000000000000 : ℝ)+(435835773043/457400000000000 : ℝ)*((971/6250 : ℝ)+(5481/50000 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (11432877746120571987/11435000000000000000 : ℝ)+(435835773043/457400000000000 : ℝ)*((971/6250 : ℝ)+(5481/50000 : ℝ))=(10000668946391863/10000000000000000 : ℝ) by norm_num, show 1+(24650461857625161/100000000000000000000 : ℝ)+(40631309309317/781250000000000000 : ℝ)=(100029851269449217737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24650461857625161/100000000000000000000 : ℝ) ≤ ((11432877746120571987/11435000000000000000 : ℝ)+2*(435835773043/457400000000000 : ℝ)*(971/6250 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (11432877746120571987/11435000000000000000 : ℝ)+2*(435835773043/457400000000000 : ℝ)*(971/6250 : ℝ)=(5000552391082453/5000000000000000 : ℝ) by norm_num, show 1+2*(24650461857625161/100000000000000000000 : ℝ)=(50024650461857625161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11432877746120571987/11435000000000000000 : ℝ)*(X 1 0+X 2 0)+(435835773043/457400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (971/6250 : ℝ)) (c := (11432877746120571987/11435000000000000000 : ℝ)) (alpha := (435835773043/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11432877746120571987/11435000000000000000 : ℝ)*(X 0 1+X 2 1)+(435835773043/457400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (971/6250 : ℝ)) (c := (11432877746120571987/11435000000000000000 : ℝ)) (alpha := (435835773043/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11432877746120571987/11435000000000000000 : ℝ)*(X 0 2+X 1 2)+(435835773043/457400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (5481/50000 : ℝ)) (hi := (971/6250 : ℝ)) (c := (11432877746120571987/11435000000000000000 : ℝ)) (alpha := (435835773043/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1831664383/10000000000 : ℝ)*X 0 0+(1086054857/2000000000 : ℝ)*X 0 1+(5218556243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350239169/10000000000 : ℝ)*X 1 0+(-1940048721/10000000000 : ℝ)*X 1 1+(2609278063/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535023887/1000000000 : ℝ)*X 2 0+(1304639123/2500000000 : ℝ)*X 2 1+(-485012159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1064560989/2500000000 : ℝ)*X 0 0+(2009896869/5000000000 : ℝ)*X 0 1+(28177193/62500000 : ℝ)*X 0 2+(1064560989/2500000000 : ℝ)*X 1 0+(2009896869/5000000000 : ℝ)*X 1 1+(28177193/62500000 : ℝ)*X 1 2+(1064560989/2500000000 : ℝ)*X 2 0+(2009896869/5000000000 : ℝ)*X 2 1+(28177193/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-114480793/625000000 : ℝ)*X 0 0+(5219654293/10000000000 : ℝ)*X 0 1+(5429168021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294460101/10000000000 : ℝ)*X 1 0+(-864718613/5000000000 : ℝ)*X 1 1+(5429167991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294460151/10000000000 : ℝ)*X 2 0+(2714583993/5000000000 : ℝ)*X 2 1+(-1729437163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2129154739/5000000000 : ℝ)*X 0 0+(1126454281/2500000000 : ℝ)*X 0 1+(4022345733/10000000000 : ℝ)*X 0 2+(2129154739/5000000000 : ℝ)*X 1 0+(1126454281/2500000000 : ℝ)*X 1 1+(4022345733/10000000000 : ℝ)*X 1 2+(2129154739/5000000000 : ℝ)*X 2 0+(1126454281/2500000000 : ℝ)*X 2 1+(4022345733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (561142169633112221018882961/142937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (798609841/100000000000000 : ℝ)*(base19) + (246679281/50000000000000 : ℝ)*(base23) + (3367569/100000000000000 : ℝ)*(upper3) + (11045127/50000000000000 : ℝ)*(upper4) + (4180021/25000000000000 : ℝ)*(upper5) + (1692536821109501/50000000000000 : ℝ)*(major0) + (1692536821109501/50000000000000 : ℝ)*(major1) + (1692536821109501/50000000000000 : ℝ)*(major2) + (2361639427531681/50000000000000 : ℝ)*(sp0) + (4723293403206907/100000000000000 : ℝ)*(sp1) + (2361646854229093/50000000000000 : ℝ)*(sp2) + (51171213098747/2500000000000 : ℝ)*(sp3) + (7673376693/50000000000000 : ℝ)*(sp4) + (2213905903/50000000000000 : ℝ)*(sp7) + (409370590352337/20000000000000 : ℝ)*(f.failure) + (1180823550454187/25000000000000 : ℝ)*(f.sum) + (79187867912747/11435000000000000000000000000 : ℝ)*base66 + (5970819381912276513/571750000000000000000000000000000 : ℝ)*base68 + (6474820790753776513/571750000000000000000000000000000 : ℝ)*base70 + (4685933142005526513/571750000000000000000000000000000 : ℝ)*base72 + (982551243819/1429375000000000000000000000 : ℝ)*base74 + (8304434632821276513/571750000000000000000000000000000 : ℝ)*base76 + (766189360214723487/571750000000000000000000000000000 : ℝ)*base77 + (424507760669276513/571750000000000000000000000000000 : ℝ)*base80 + (17035653437827/11435000000000000000000000000 : ℝ)*base82 + (18649/80000000000000000000 : ℝ)*base89 + (18649/80000000000000000000 : ℝ)*base91 + (18649/80000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38322949871209401197391/5717500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1042775987/100000000000000 : ℝ)*(base19) + (591374297/50000000000000 : ℝ)*(base23) + (28810553/20000000000000 : ℝ)*(upper3) + (36943541/100000000000000 : ℝ)*(lower4) + (39382103/25000000000000 : ℝ)*(upper5) + (855166471602379/25000000000000 : ℝ)*(major0) + (855166471602379/25000000000000 : ℝ)*(major1) + (855166471602379/25000000000000 : ℝ)*(major2) + (1888923429/12500000000000 : ℝ)*(sp1) + (17495835469/100000000000000 : ℝ)*(sp2) + (4772957030369487/100000000000000 : ℝ)*(sp4) + (4772940876206069/100000000000000 : ℝ)*(sp5) + (298308646986589/6250000000000 : ℝ)*(sp6) + (206837451902467/10000000000000 : ℝ)*(sp7) + (206837451902467/10000000000000 : ℝ)*(f.failure) + (4772957030369487/100000000000000 : ℝ)*(f.sum) + (22535361689573/5717500000000000000000000000 : ℝ)*base66 + (1478666427017242927/285875000000000000000000000000000 : ℝ)*base68 + (3742668475302507073/285875000000000000000000000000000 : ℝ)*base69 + (689440314265007073/285875000000000000000000000000000 : ℝ)*base71 + (3062450271437/1429375000000000000000000000 : ℝ)*base74 + (351967915398492927/285875000000000000000000000000000 : ℝ)*base76 + (1477356960502632073/285875000000000000000000000000000 : ℝ)*base77 + (175160222983117927/285875000000000000000000000000000 : ℝ)*base80 + (13276290206001/2858750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (458341/40000000000000000000 : ℝ)*base90 + (458341/40000000000000000000 : ℝ)*base92 + (458341/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1537_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (971/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5481/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1537_s5_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-457925673/2500000000 : ℝ)*x 0 + (217201027/400000000 : ℝ)*x 1 + (1304694851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (457925673/2500000000 : ℝ)^4571 ≤ (1402668869031/12500000000000 : ℝ)^3547 := by
    have hnat : (457925673 : ℕ)^4571*12500000000000^3547 ≤ 1402668869031^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457925673 2500000000 1402668869031 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217201027/400000000 : ℝ)^4571 ≤ (910480388171/2000000000000 : ℝ)^3547 := by
    have hnat : (217201027 : ℕ)^4571*2000000000000^3547 ≤ 910480388171^3547*400000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217201027 400000000 910480388171 2000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304694851/2500000000 : ℝ)^4571 ≤ (8650925923903/20000000000000 : ℝ)^3547 := by
    have hnat : (1304694851 : ℕ)^4571*20000000000000^3547 ≤ 8650925923903^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304694851 2500000000 8650925923903 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-457925673/2500000000 : ℝ), (217201027/400000000 : ℝ), (1304694851/2500000000 : ℝ)] ![(1402668869031/12500000000000 : ℝ), (910480388171/2000000000000 : ℝ), (8650925923903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-457925673/2500000000 : ℝ)|^4571 ≤ (1402668869031/12500000000000 : ℝ)^3547
        have hw : |(-457925673/2500000000 : ℝ)|=(457925673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217201027/400000000 : ℝ)|^4571 ≤ (910480388171/2000000000000 : ℝ)^3547
        have hw : |(217201027/400000000 : ℝ)|=(217201027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304694851/2500000000 : ℝ)|^4571 ≤ (8650925923903/20000000000000 : ℝ)^3547
        have hw : |(1304694851/2500000000 : ℝ)|=(1304694851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267508659/500000000 : ℝ)*x 0 + (-1939840021/10000000000 : ℝ)*x 1 + (5218779429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267508659/500000000 : ℝ)^4571 ≤ (22331561271059/50000000000000 : ℝ)^3547 := by
    have hnat : (267508659 : ℕ)^4571*50000000000000^3547 ≤ 22331561271059^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267508659 500000000 22331561271059 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939840021/10000000000 : ℝ)^4571 ≤ (12082247555559/100000000000000 : ℝ)^3547 := by
    have hnat : (1939840021 : ℕ)^4571*100000000000000^3547 ≤ 12082247555559^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939840021 10000000000 12082247555559 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218779429/10000000000 : ℝ)^4571 ≤ (43254629886541/100000000000000 : ℝ)^3547 := by
    have hnat : (5218779429 : ℕ)^4571*100000000000000^3547 ≤ 43254629886541^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218779429 10000000000 43254629886541 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267508659/500000000 : ℝ), (-1939840021/10000000000 : ℝ), (5218779429/10000000000 : ℝ)] ![(22331561271059/50000000000000 : ℝ), (12082247555559/100000000000000 : ℝ), (43254629886541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267508659/500000000 : ℝ)|^4571 ≤ (22331561271059/50000000000000 : ℝ)^3547
        have hw : |(267508659/500000000 : ℝ)|=(267508659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1939840021/10000000000 : ℝ)|^4571 ≤ (12082247555559/100000000000000 : ℝ)^3547
        have hw : |(-1939840021/10000000000 : ℝ)|=(1939840021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218779429/10000000000 : ℝ)|^4571 ≤ (43254629886541/100000000000000 : ℝ)^3547
        have hw : |(5218779429/10000000000 : ℝ)|=(5218779429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675086607/5000000000 : ℝ)*x 0 + (5218779399/10000000000 : ℝ)*x 1 + (-387968003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675086607/5000000000 : ℝ)^4571 ≤ (44663122907889/100000000000000 : ℝ)^3547 := by
    have hnat : (2675086607 : ℕ)^4571*100000000000000^3547 ≤ 44663122907889^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675086607 5000000000 44663122907889 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218779399/10000000000 : ℝ)^4571 ≤ (4325462956611/10000000000000 : ℝ)^3547 := by
    have hnat : (5218779399 : ℕ)^4571*10000000000000^3547 ≤ 4325462956611^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218779399 10000000000 4325462956611 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387968003/2000000000 : ℝ)^4571 ≤ (12082247507399/100000000000000 : ℝ)^3547 := by
    have hnat : (387968003 : ℕ)^4571*100000000000000^3547 ≤ 12082247507399^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387968003 2000000000 12082247507399 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675086607/5000000000 : ℝ), (5218779399/10000000000 : ℝ), (-387968003/2000000000 : ℝ)] ![(44663122907889/100000000000000 : ℝ), (4325462956611/10000000000000 : ℝ), (12082247507399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675086607/5000000000 : ℝ)|^4571 ≤ (44663122907889/100000000000000 : ℝ)^3547
        have hw : |(2675086607/5000000000 : ℝ)|=(2675086607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218779399/10000000000 : ℝ)|^4571 ≤ (4325462956611/10000000000000 : ℝ)^3547
        have hw : |(5218779399/10000000000 : ℝ)|=(5218779399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387968003/2000000000 : ℝ)|^4571 ≤ (12082247507399/100000000000000 : ℝ)^3547
        have hw : |(-387968003/2000000000 : ℝ)|=(387968003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258267679/10000000000 : ℝ)*x 0 + (4020334793/10000000000 : ℝ)*x 1 + (4507804093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258267679/10000000000 : ℝ)^4571 ≤ (2080053503589/6250000000000 : ℝ)^3547 := by
    have hnat : (4258267679 : ℕ)^4571*6250000000000^3547 ≤ 2080053503589^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258267679 10000000000 2080053503589 6250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4020334793/10000000000 : ℝ)^4571 ≤ (3863001218503/12500000000000 : ℝ)^3547 := by
    have hnat : (4020334793 : ℕ)^4571*12500000000000^3547 ≤ 3863001218503^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020334793 10000000000 3863001218503 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507804093/10000000000 : ℝ)^4571 ≤ (1432605367219/4000000000000 : ℝ)^3547 := by
    have hnat : (4507804093 : ℕ)^4571*4000000000000^3547 ≤ 1432605367219^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507804093 10000000000 1432605367219 4000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258267679/10000000000 : ℝ), (4020334793/10000000000 : ℝ), (4507804093/10000000000 : ℝ)] ![(2080053503589/6250000000000 : ℝ), (3863001218503/12500000000000 : ℝ), (1432605367219/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258267679/10000000000 : ℝ)|^4571 ≤ (2080053503589/6250000000000 : ℝ)^3547
        have hw : |(4258267679/10000000000 : ℝ)|=(4258267679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4020334793/10000000000 : ℝ)|^4571 ≤ (3863001218503/12500000000000 : ℝ)^3547
        have hw : |(4020334793/10000000000 : ℝ)|=(4020334793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507804093/10000000000 : ℝ)|^4571 ≤ (1432605367219/4000000000000 : ℝ)^3547
        have hw : |(4507804093/10000000000 : ℝ)|=(4507804093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-915865371/5000000000 : ℝ)*x 0 + (1304967901/2500000000 : ℝ)*x 1 + (2714462677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (915865371/5000000000 : ℝ)^4571 ≤ (11221572401399/100000000000000 : ℝ)^3547 := by
    have hnat : (915865371 : ℕ)^4571*100000000000000^3547 ≤ 11221572401399^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915865371 5000000000 11221572401399 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304967901/2500000000 : ℝ)^4571 ≤ (4326629580781/10000000000000 : ℝ)^3547 := by
    have hnat : (1304967901 : ℕ)^4571*10000000000000^3547 ≤ 4326629580781^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304967901 2500000000 4326629580781 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714462677/5000000000 : ℝ)^4571 ≤ (45512131773951/100000000000000 : ℝ)^3547 := by
    have hnat : (2714462677 : ℕ)^4571*100000000000000^3547 ≤ 45512131773951^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714462677 5000000000 45512131773951 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-915865371/5000000000 : ℝ), (1304967901/2500000000 : ℝ), (2714462677/5000000000 : ℝ)] ![(11221572401399/100000000000000 : ℝ), (4326629580781/10000000000000 : ℝ), (45512131773951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-915865371/5000000000 : ℝ)|^4571 ≤ (11221572401399/100000000000000 : ℝ)^3547
        have hw : |(-915865371/5000000000 : ℝ)|=(915865371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304967901/2500000000 : ℝ)|^4571 ≤ (4326629580781/10000000000000 : ℝ)^3547
        have hw : |(1304967901/2500000000 : ℝ)|=(1304967901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714462677/5000000000 : ℝ)|^4571 ≤ (45512131773951/100000000000000 : ℝ)^3547
        have hw : |(2714462677/5000000000 : ℝ)|=(2714462677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323629869/2500000000 : ℝ)*x 0 + (-864847429/5000000000 : ℝ)*x 1 + (542892387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323629869/2500000000 : ℝ)^4571 ≤ (8813060317503/20000000000000 : ℝ)^3547 := by
    have hnat : (1323629869 : ℕ)^4571*20000000000000^3547 ≤ 8813060317503^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323629869 2500000000 8813060317503 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864847429/5000000000 : ℝ)^4571 ≤ (1302822831533/12500000000000 : ℝ)^3547 := by
    have hnat : (864847429 : ℕ)^4571*12500000000000^3547 ≤ 1302822831533^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864847429 5000000000 1302822831533 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542892387/1000000000 : ℝ)^4571 ≤ (56890144677/125000000000 : ℝ)^3547 := by
    have hnat : (542892387 : ℕ)^4571*125000000000^3547 ≤ 56890144677^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542892387 1000000000 56890144677 125000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323629869/2500000000 : ℝ), (-864847429/5000000000 : ℝ), (542892387/1000000000 : ℝ)] ![(8813060317503/20000000000000 : ℝ), (1302822831533/12500000000000 : ℝ), (56890144677/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323629869/2500000000 : ℝ)|^4571 ≤ (8813060317503/20000000000000 : ℝ)^3547
        have hw : |(1323629869/2500000000 : ℝ)|=(1323629869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-864847429/5000000000 : ℝ)|^4571 ≤ (1302822831533/12500000000000 : ℝ)^3547
        have hw : |(-864847429/5000000000 : ℝ)|=(864847429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542892387/1000000000 : ℝ)|^4571 ≤ (56890144677/125000000000 : ℝ)^3547
        have hw : |(542892387/1000000000 : ℝ)|=(542892387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323629511/2500000000 : ℝ)*x 0 + (1357231189/2500000000 : ℝ)*x 1 + (-432423901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323629511/2500000000 : ℝ)^4571 ≤ (8813057245701/20000000000000 : ℝ)^3547 := by
    have hnat : (1323629511 : ℕ)^4571*20000000000000^3547 ≤ 8813057245701^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323629511 2500000000 8813057245701 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357231189/2500000000 : ℝ)^4571 ≤ (1820485012539/4000000000000 : ℝ)^3547 := by
    have hnat : (1357231189 : ℕ)^4571*4000000000000^3547 ≤ 1820485012539^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357231189 2500000000 1820485012539 4000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432423901/2500000000 : ℝ)^4571 ≤ (10422588445147/100000000000000 : ℝ)^3547 := by
    have hnat : (432423901 : ℕ)^4571*100000000000000^3547 ≤ 10422588445147^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432423901 2500000000 10422588445147 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323629511/2500000000 : ℝ), (1357231189/2500000000 : ℝ), (-432423901/2500000000 : ℝ)] ![(8813057245701/20000000000000 : ℝ), (1820485012539/4000000000000 : ℝ), (10422588445147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323629511/2500000000 : ℝ)|^4571 ≤ (8813057245701/20000000000000 : ℝ)^3547
        have hw : |(1323629511/2500000000 : ℝ)|=(1323629511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357231189/2500000000 : ℝ)|^4571 ≤ (1820485012539/4000000000000 : ℝ)^3547
        have hw : |(1357231189/2500000000 : ℝ)|=(1357231189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432423901/2500000000 : ℝ)|^4571 ≤ (10422588445147/100000000000000 : ℝ)^3547
        have hw : |(-432423901/2500000000 : ℝ)|=(432423901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s5_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851666381/2000000000 : ℝ)*x 0 + (2252640921/5000000000 : ℝ)*x 1 + (4022876027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851666381/2000000000 : ℝ)^4571 ≤ (16640751468459/50000000000000 : ℝ)^3547 := by
    have hnat : (851666381 : ℕ)^4571*50000000000000^3547 ≤ 16640751468459^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851666381 2000000000 16640751468459 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252640921/5000000000 : ℝ)^4571 ≤ (35789311293037/100000000000000 : ℝ)^3547 := by
    have hnat : (2252640921 : ℕ)^4571*100000000000000^3547 ≤ 35789311293037^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252640921 5000000000 35789311293037 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022876027/10000000000 : ℝ)^4571 ≤ (15464592879511/50000000000000 : ℝ)^3547 := by
    have hnat : (4022876027 : ℕ)^4571*50000000000000^3547 ≤ 15464592879511^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022876027 10000000000 15464592879511 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851666381/2000000000 : ℝ), (2252640921/5000000000 : ℝ), (4022876027/10000000000 : ℝ)] ![(16640751468459/50000000000000 : ℝ), (35789311293037/100000000000000 : ℝ), (15464592879511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851666381/2000000000 : ℝ)|^4571 ≤ (16640751468459/50000000000000 : ℝ)^3547
        have hw : |(851666381/2000000000 : ℝ)|=(851666381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252640921/5000000000 : ℝ)|^4571 ≤ (35789311293037/100000000000000 : ℝ)^3547
        have hw : |(2252640921/5000000000 : ℝ)|=(2252640921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022876027/10000000000 : ℝ)|^4571 ≤ (15464592879511/50000000000000 : ℝ)^3547
        have hw : |(4022876027/10000000000 : ℝ)|=(4022876027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (344/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2751/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2751/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2751/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2751/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2751/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2751/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2751/25000 : ℝ) ^ (4569/1024 : ℝ) ≤ (2645154640236623/50000000000000000000 : ℝ) := by
    have hpowers : (2751/25000 : ℝ)^4569 ≤ (2645154640236623/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2751 : ℕ)^4569*50000000000000000000^1024 ≤ 2645154640236623^1024*25000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2751 25000 2645154640236623 50000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2751/25000 : ℝ)) (X := (2645154640236623/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4569/1024 : ℝ) ≤ (6081616627813927/25000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4569 ≤ (6081616627813927/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4569*25000000000000000000^1024 ≤ 6081616627813927^1024*10000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 6081616627813927 25000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (6081616627813927/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002645154640236623/25000000000000000000 : ℝ) ≤ (10000237122099229/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (25002645154640236623/25000000000000000000 : ℝ)^1024 ≤ (10000237122099229/10000000000000000 : ℝ)^4569 := by
      have hnat : (25002645154640236623 : ℕ)^1024*10000000000000000^4569 ≤ 10000237122099229^4569*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002645154640236623 25000000000000000000 10000237122099229 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000237122099229/10000000000000000 : ℝ)) (X := (25002645154640236623/25000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014808387895864477/50000000000000000000 : ℝ) ≤ (10000663692154093/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (50014808387895864477/50000000000000000000 : ℝ)^1024 ≤ (10000663692154093/10000000000000000 : ℝ)^4569 := by
      have hnat : (50014808387895864477 : ℕ)^1024*10000000000000000^4569 ≤ 10000663692154093^4569*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014808387895864477 50000000000000000000 10000663692154093 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000663692154093/10000000000000000 : ℝ)) (X := (50014808387895864477/50000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506081616627813927/12500000000000000000 : ℝ) ≤ (10001090262208957/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (12506081616627813927/12500000000000000000 : ℝ)^1024 ≤ (10001090262208957/10000000000000000 : ℝ)^4569 := by
      have hnat : (12506081616627813927 : ℕ)^1024*10000000000000000^4569 ≤ 10001090262208957^4569*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506081616627813927 12500000000000000000 10001090262208957 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001090262208957/10000000000000000 : ℝ)) (X := (12506081616627813927/12500000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2645154640236623/50000000000000000000 : ℝ) ≤ ((22425837887984847191/22430000000000000000 : ℝ)+2*(26660628429/28037500000000 : ℝ)*(2751/25000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (22425837887984847191/22430000000000000000 : ℝ)+2*(26660628429/28037500000000 : ℝ)*(2751/25000 : ℝ)=(10000237122099229/10000000000000000 : ℝ) by norm_num, show 1+2*(2645154640236623/50000000000000000000 : ℝ)=(25002645154640236623/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6081616627813927/25000000000000000000 : ℝ)+(2645154640236623/50000000000000000000 : ℝ) ≤ ((22425837887984847191/22430000000000000000 : ℝ)+(26660628429/28037500000000 : ℝ)*((1549/10000 : ℝ)+(2751/25000 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (22425837887984847191/22430000000000000000 : ℝ)+(26660628429/28037500000000 : ℝ)*((1549/10000 : ℝ)+(2751/25000 : ℝ))=(10000663692154093/10000000000000000 : ℝ) by norm_num, show 1+(6081616627813927/25000000000000000000 : ℝ)+(2645154640236623/50000000000000000000 : ℝ)=(50014808387895864477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6081616627813927/25000000000000000000 : ℝ) ≤ ((22425837887984847191/22430000000000000000 : ℝ)+2*(26660628429/28037500000000 : ℝ)*(1549/10000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (22425837887984847191/22430000000000000000 : ℝ)+2*(26660628429/28037500000000 : ℝ)*(1549/10000 : ℝ)=(10001090262208957/10000000000000000 : ℝ) by norm_num, show 1+2*(6081616627813927/25000000000000000000 : ℝ)=(12506081616627813927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22425837887984847191/22430000000000000000 : ℝ)*(X 1 0+X 2 0)+(26660628429/28037500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (2751/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (22425837887984847191/22430000000000000000 : ℝ)) (alpha := (26660628429/28037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22425837887984847191/22430000000000000000 : ℝ)*(X 0 1+X 2 1)+(26660628429/28037500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (2751/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (22425837887984847191/22430000000000000000 : ℝ)) (alpha := (26660628429/28037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22425837887984847191/22430000000000000000 : ℝ)*(X 0 2+X 1 2)+(26660628429/28037500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (2751/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (22425837887984847191/22430000000000000000 : ℝ)) (alpha := (26660628429/28037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-457925673/2500000000 : ℝ)*X 0 0+(217201027/400000000 : ℝ)*X 0 1+(1304694851/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267508659/500000000 : ℝ)*X 1 0+(-1939840021/10000000000 : ℝ)*X 1 1+(5218779429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675086607/5000000000 : ℝ)*X 2 0+(5218779399/10000000000 : ℝ)*X 2 1+(-387968003/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4258267679/10000000000 : ℝ)*X 0 0+(4020334793/10000000000 : ℝ)*X 0 1+(4507804093/10000000000 : ℝ)*X 0 2+(4258267679/10000000000 : ℝ)*X 1 0+(4020334793/10000000000 : ℝ)*X 1 1+(4507804093/10000000000 : ℝ)*X 1 2+(4258267679/10000000000 : ℝ)*X 2 0+(4020334793/10000000000 : ℝ)*X 2 1+(4507804093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-915865371/5000000000 : ℝ)*X 0 0+(1304967901/2500000000 : ℝ)*X 0 1+(2714462677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323629869/2500000000 : ℝ)*X 1 0+(-864847429/5000000000 : ℝ)*X 1 1+(542892387/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323629511/2500000000 : ℝ)*X 2 0+(1357231189/2500000000 : ℝ)*X 2 1+(-432423901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((851666381/2000000000 : ℝ)*X 0 0+(2252640921/5000000000 : ℝ)*X 0 1+(4022876027/10000000000 : ℝ)*X 0 2+(851666381/2000000000 : ℝ)*X 1 0+(2252640921/5000000000 : ℝ)*X 1 1+(4022876027/10000000000 : ℝ)*X 1 2+(851666381/2000000000 : ℝ)*X 2 0+(2252640921/5000000000 : ℝ)*X 2 1+(4022876027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1661048903092913828394866913/140187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25778963/1250000000000 : ℝ)*(base19) + (973949867/50000000000000 : ℝ)*(base23) + (9663803/12500000000000 : ℝ)*(lower2) + (72725459/25000000000000 : ℝ)*(upper3) + (24566103/12500000000000 : ℝ)*(upper5) + (848165018494081/25000000000000 : ℝ)*(major0) + (848165018494081/25000000000000 : ℝ)*(major1) + (135706402959053/4000000000000 : ℝ)*(major2) + (946769174104813/20000000000000 : ℝ)*(sp0) + (4733877450165357/100000000000000 : ℝ)*(sp1) + (4733877564582663/100000000000000 : ℝ)*(sp2) + (20514248898587/1000000000000 : ℝ)*(sp3) + (8410489583/25000000000000 : ℝ)*(sp4) + (15350652673/100000000000000 : ℝ)*(sp7) + (512860060127843/25000000000000 : ℝ)*(f.failure) + (4733879512482397/100000000000000 : ℝ)*(f.sum) + (28319201186131/11215000000000000000000000000 : ℝ)*base66 + (7941706249858773529/560750000000000000000000000000000 : ℝ)*base68 + (213638112698537877/89720000000000000000000000000000 : ℝ)*base70 + (5858255581560773529/560750000000000000000000000000000 : ℝ)*base72 + (11769980116849/11215000000000000000000000000 : ℝ)*base73 + (697438488073662123/89720000000000000000000000000000 : ℝ)*base75 + (5350424983283073529/560750000000000000000000000000000 : ℝ)*base78 + (5078009300185073529/560750000000000000000000000000000 : ℝ)*base80 + (4703949764439/5607500000000000000000000000 : ℝ)*base81 + (73211/100000000000000000000 : ℝ)*base89 + (73211/100000000000000000000 : ℝ)*base91 + (926789/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1033581593503048764935995899/112150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2039986897/100000000000000 : ℝ)*(base19) + (146431241/25000000000000 : ℝ)*(base23) + (21349431/50000000000000 : ℝ)*(upper2) + (2588859/2500000000000 : ℝ)*(upper3) + (231550139/100000000000000 : ℝ)*(upper5) + (342821332678337/10000000000000 : ℝ)*(major0) + (342821332678337/10000000000000 : ℝ)*(major1) + (342821332678337/10000000000000 : ℝ)*(major2) + (8636507823/50000000000000 : ℝ)*(sp0) + (22939220727/100000000000000 : ℝ)*(sp1) + (2391735421249937/50000000000000 : ℝ)*(sp4) + (597932892038487/12500000000000 : ℝ)*(sp5) + (956697505958111/20000000000000 : ℝ)*(sp6) + (2072938230849073/100000000000000 : ℝ)*(sp7) + (2072938230849073/100000000000000 : ℝ)*(f.failure) + (4783488115515519/100000000000000 : ℝ)*(f.sum) + (48894971399593/2243000000000000000000000000 : ℝ)*base65 + (1044805522952198633/224300000000000000000000000000000 : ℝ)*base68 + (243458849130101367/224300000000000000000000000000000 : ℝ)*base69 + (856958585929101367/224300000000000000000000000000000 : ℝ)*base71 + (1029594128087/448600000000000000000000000 : ℝ)*base73 + (2584278246628798633/224300000000000000000000000000000 : ℝ)*base76 + (1039047554573901367/224300000000000000000000000000000 : ℝ)*base77 + (1105874697841601367/224300000000000000000000000000000 : ℝ)*base79 + (172136166427/89720000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1819079/400000000000000000000 : ℝ)*base90 + (1819079/400000000000000000000 : ℝ)*base92 + (1819079/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1537_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2751/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1537_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1537_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1537_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1537_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1537_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
