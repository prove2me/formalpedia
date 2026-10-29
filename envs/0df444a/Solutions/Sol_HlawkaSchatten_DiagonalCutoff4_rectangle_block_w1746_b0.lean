-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1746_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:17:58.489664+00:00
-- url     : https://prove2.me/submissions/4584f0df-5885-47eb-bfdf-201c00989799

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
theorem support_rectangle_w1746_s0_0 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1196579433/10000000000 : ℝ)*x 0 + (352680397/625000000 : ℝ)*x 1 + (4971699359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1196579433/10000000000 : ℝ)^5711 ≤ (3762385611881/50000000000000 : ℝ)^4687 := by
    have hnat : (1196579433 : ℕ)^5711*50000000000000^4687 ≤ 3762385611881^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196579433 10000000000 3762385611881 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352680397/625000000 : ℝ)^5711 ≤ (49797798555951/100000000000000 : ℝ)^4687 := by
    have hnat : (352680397 : ℕ)^5711*100000000000000^4687 ≤ 49797798555951^4687*625000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352680397 625000000 49797798555951 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4971699359/10000000000 : ℝ)^5711 ≤ (10669357552469/25000000000000 : ℝ)^4687 := by
    have hnat : (4971699359 : ℕ)^5711*25000000000000^4687 ≤ 10669357552469^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971699359 10000000000 10669357552469 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1196579433/10000000000 : ℝ), (352680397/625000000 : ℝ), (4971699359/10000000000 : ℝ)] ![(3762385611881/50000000000000 : ℝ), (49797798555951/100000000000000 : ℝ), (10669357552469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1196579433/10000000000 : ℝ)|^5711 ≤ (3762385611881/50000000000000 : ℝ)^4687
        have hw : |(-1196579433/10000000000 : ℝ)|=(1196579433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352680397/625000000 : ℝ)|^5711 ≤ (49797798555951/100000000000000 : ℝ)^4687
        have hw : |(352680397/625000000 : ℝ)|=(352680397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4971699359/10000000000 : ℝ)|^5711 ≤ (10669357552469/25000000000000 : ℝ)^4687
        have hw : |(4971699359/10000000000 : ℝ)|=(4971699359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_1 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376519937/10000000000 : ℝ)*x 0 + (-778683699/5000000000 : ℝ)*x 1 + (310731229/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376519937/10000000000 : ℝ)^5711 ≤ (5868567378373/12500000000000 : ℝ)^4687 := by
    have hnat : (5376519937 : ℕ)^5711*12500000000000^4687 ≤ 5868567378373^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376519937 10000000000 5868567378373 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778683699/5000000000 : ℝ)^5711 ≤ (5187013779927/50000000000000 : ℝ)^4687 := by
    have hnat : (778683699 : ℕ)^5711*50000000000000^4687 ≤ 5187013779927^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778683699 5000000000 5187013779927 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310731229/625000000 : ℝ)^5711 ≤ (42677433400021/100000000000000 : ℝ)^4687 := by
    have hnat : (310731229 : ℕ)^5711*100000000000000^4687 ≤ 42677433400021^4687*625000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310731229 625000000 42677433400021 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376519937/10000000000 : ℝ), (-778683699/5000000000 : ℝ), (310731229/625000000 : ℝ)] ![(5868567378373/12500000000000 : ℝ), (5187013779927/50000000000000 : ℝ), (42677433400021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376519937/10000000000 : ℝ)|^5711 ≤ (5868567378373/12500000000000 : ℝ)^4687
        have hw : |(5376519937/10000000000 : ℝ)|=(5376519937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-778683699/5000000000 : ℝ)|^5711 ≤ (5187013779927/50000000000000 : ℝ)^4687
        have hw : |(-778683699/5000000000 : ℝ)|=(778683699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310731229/625000000 : ℝ)|^5711 ≤ (42677433400021/100000000000000 : ℝ)^4687
        have hw : |(310731229/625000000 : ℝ)|=(310731229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_2 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376521001/10000000000 : ℝ)*x 0 + (4971699047/10000000000 : ℝ)*x 1 + (-778683399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376521001/10000000000 : ℝ)^5711 ≤ (46948550347851/100000000000000 : ℝ)^4687 := by
    have hnat : (5376521001 : ℕ)^5711*100000000000000^4687 ≤ 46948550347851^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376521001 10000000000 46948550347851 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4971699047/10000000000 : ℝ)^5711 ≤ (8535485389303/20000000000000 : ℝ)^4687 := by
    have hnat : (4971699047 : ℕ)^5711*20000000000000^4687 ≤ 8535485389303^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971699047 10000000000 8535485389303 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (778683399/5000000000 : ℝ)^5711 ≤ (10374022689901/100000000000000 : ℝ)^4687 := by
    have hnat : (778683399 : ℕ)^5711*100000000000000^4687 ≤ 10374022689901^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778683399 5000000000 10374022689901 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376521001/10000000000 : ℝ), (4971699047/10000000000 : ℝ), (-778683399/5000000000 : ℝ)] ![(46948550347851/100000000000000 : ℝ), (8535485389303/20000000000000 : ℝ), (10374022689901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376521001/10000000000 : ℝ)|^5711 ≤ (46948550347851/100000000000000 : ℝ)^4687
        have hw : |(5376521001/10000000000 : ℝ)|=(5376521001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4971699047/10000000000 : ℝ)|^5711 ≤ (8535485389303/20000000000000 : ℝ)^4687
        have hw : |(4971699047/10000000000 : ℝ)|=(4971699047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-778683399/5000000000 : ℝ)|^5711 ≤ (10374022689901/100000000000000 : ℝ)^4687
        have hw : |(-778683399/5000000000 : ℝ)|=(778683399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_3 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (796696891/2000000000 : ℝ)*x 0 + (2980279427/10000000000 : ℝ)*x 1 + (5149547089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796696891/2000000000 : ℝ)^5711 ≤ (6515683112701/20000000000000 : ℝ)^4687 := by
    have hnat : (796696891 : ℕ)^5711*20000000000000^4687 ≤ 6515683112701^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796696891 2000000000 6515683112701 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2980279427/10000000000 : ℝ)^5711 ≤ (4575350974799/20000000000000 : ℝ)^4687 := by
    have hnat : (2980279427 : ℕ)^5711*20000000000000^4687 ≤ 4575350974799^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980279427 10000000000 4575350974799 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149547089/10000000000 : ℝ)^5711 ≤ (4454482955481/10000000000000 : ℝ)^4687 := by
    have hnat : (5149547089 : ℕ)^5711*10000000000000^4687 ≤ 4454482955481^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149547089 10000000000 4454482955481 10000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796696891/2000000000 : ℝ), (2980279427/10000000000 : ℝ), (5149547089/10000000000 : ℝ)] ![(6515683112701/20000000000000 : ℝ), (4575350974799/20000000000000 : ℝ), (4454482955481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796696891/2000000000 : ℝ)|^5711 ≤ (6515683112701/20000000000000 : ℝ)^4687
        have hw : |(796696891/2000000000 : ℝ)|=(796696891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2980279427/10000000000 : ℝ)|^5711 ≤ (4575350974799/20000000000000 : ℝ)^4687
        have hw : |(2980279427/10000000000 : ℝ)|=(2980279427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149547089/10000000000 : ℝ)|^5711 ≤ (4454482955481/10000000000000 : ℝ)^4687
        have hw : |(5149547089/10000000000 : ℝ)|=(5149547089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_4 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29950773/250000000 : ℝ)*x 0 + (1247226901/2500000000 : ℝ)*x 1 + (2812550381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29950773/250000000 : ℝ)^5711 ≤ (470993417339/6250000000000 : ℝ)^4687 := by
    have hnat : (29950773 : ℕ)^5711*6250000000000^4687 ≤ 470993417339^4687*250000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29950773 250000000 470993417339 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247226901/2500000000 : ℝ)^5711 ≤ (1071437192761/2500000000000 : ℝ)^4687 := by
    have hnat : (1247226901 : ℕ)^5711*2500000000000^4687 ≤ 1071437192761^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247226901 2500000000 1071437192761 2500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812550381/5000000000 : ℝ)^5711 ≤ (12401654398159/25000000000000 : ℝ)^4687 := by
    have hnat : (2812550381 : ℕ)^5711*25000000000000^4687 ≤ 12401654398159^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812550381 5000000000 12401654398159 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29950773/250000000 : ℝ), (1247226901/2500000000 : ℝ), (2812550381/5000000000 : ℝ)] ![(470993417339/6250000000000 : ℝ), (1071437192761/2500000000000 : ℝ), (12401654398159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29950773/250000000 : ℝ)|^5711 ≤ (470993417339/6250000000000 : ℝ)^4687
        have hw : |(-29950773/250000000 : ℝ)|=(29950773/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1247226901/2500000000 : ℝ)|^5711 ≤ (1071437192761/2500000000000 : ℝ)^4687
        have hw : |(1247226901/2500000000 : ℝ)|=(1247226901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812550381/5000000000 : ℝ)|^5711 ≤ (12401654398159/25000000000000 : ℝ)^4687
        have hw : |(2812550381/5000000000 : ℝ)|=(2812550381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_5 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197101549/10000000000 : ℝ)*x 0 + (-451982703/5000000000 : ℝ)*x 1 + (2812550437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197101549/10000000000 : ℝ)^5711 ≤ (5630820449511/12500000000000 : ℝ)^4687 := by
    have hnat : (5197101549 : ℕ)^5711*12500000000000^4687 ≤ 5630820449511^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197101549 10000000000 5630820449511 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451982703/5000000000 : ℝ)^5711 ≤ (5346817591403/100000000000000 : ℝ)^4687 := by
    have hnat : (451982703 : ℕ)^5711*100000000000000^4687 ≤ 5346817591403^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451982703 5000000000 5346817591403 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812550437/5000000000 : ℝ)^5711 ≤ (12401654699033/25000000000000 : ℝ)^4687 := by
    have hnat : (2812550437 : ℕ)^5711*25000000000000^4687 ≤ 12401654699033^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812550437 5000000000 12401654699033 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197101549/10000000000 : ℝ), (-451982703/5000000000 : ℝ), (2812550437/5000000000 : ℝ)] ![(5630820449511/12500000000000 : ℝ), (5346817591403/100000000000000 : ℝ), (12401654699033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197101549/10000000000 : ℝ)|^5711 ≤ (5630820449511/12500000000000 : ℝ)^4687
        have hw : |(5197101549/10000000000 : ℝ)|=(5197101549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451982703/5000000000 : ℝ)|^5711 ≤ (5346817591403/100000000000000 : ℝ)^4687
        have hw : |(-451982703/5000000000 : ℝ)|=(451982703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812550437/5000000000 : ℝ)|^5711 ≤ (12401654699033/25000000000000 : ℝ)^4687
        have hw : |(2812550437/5000000000 : ℝ)|=(2812550437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_6 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039420253/2000000000 : ℝ)*x 0 + (5625100833/10000000000 : ℝ)*x 1 + (-903965883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039420253/2000000000 : ℝ)^5711 ≤ (11261640149169/25000000000000 : ℝ)^4687 := by
    have hnat : (1039420253 : ℕ)^5711*25000000000000^4687 ≤ 11261640149169^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039420253 2000000000 11261640149169 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5625100833/10000000000 : ℝ)^5711 ≤ (49606618355567/100000000000000 : ℝ)^4687 := by
    have hnat : (5625100833 : ℕ)^5711*100000000000000^4687 ≤ 49606618355567^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625100833 10000000000 49606618355567 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903965883/10000000000 : ℝ)^5711 ≤ (5346821029191/100000000000000 : ℝ)^4687 := by
    have hnat : (903965883 : ℕ)^5711*100000000000000^4687 ≤ 5346821029191^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903965883 10000000000 5346821029191 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039420253/2000000000 : ℝ), (5625100833/10000000000 : ℝ), (-903965883/10000000000 : ℝ)] ![(11261640149169/25000000000000 : ℝ), (49606618355567/100000000000000 : ℝ), (5346821029191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039420253/2000000000 : ℝ)|^5711 ≤ (11261640149169/25000000000000 : ℝ)^4687
        have hw : |(1039420253/2000000000 : ℝ)|=(1039420253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5625100833/10000000000 : ℝ)|^5711 ≤ (49606618355567/100000000000000 : ℝ)^4687
        have hw : |(5625100833/10000000000 : ℝ)|=(5625100833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903965883/10000000000 : ℝ)|^5711 ≤ (5346821029191/100000000000000 : ℝ)^4687
        have hw : |(-903965883/10000000000 : ℝ)|=(903965883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s0_7 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (997043987/2500000000 : ℝ)*x 0 + (5093929519/10000000000 : ℝ)*x 1 + (3037761837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997043987/2500000000 : ℝ)^5711 ≤ (8156293257311/25000000000000 : ℝ)^4687 := by
    have hnat : (997043987 : ℕ)^5711*25000000000000^4687 ≤ 8156293257311^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997043987 2500000000 8156293257311 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5093929519/10000000000 : ℝ)^5711 ≤ (1758372295613/4000000000000 : ℝ)^4687 := by
    have hnat : (5093929519 : ℕ)^5711*4000000000000^4687 ≤ 1758372295613^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093929519 10000000000 1758372295613 4000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3037761837/10000000000 : ℝ)^5711 ≤ (11707759785847/50000000000000 : ℝ)^4687 := by
    have hnat : (3037761837 : ℕ)^5711*50000000000000^4687 ≤ 11707759785847^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037761837 10000000000 11707759785847 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(997043987/2500000000 : ℝ), (5093929519/10000000000 : ℝ), (3037761837/10000000000 : ℝ)] ![(8156293257311/25000000000000 : ℝ), (1758372295613/4000000000000 : ℝ), (11707759785847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(997043987/2500000000 : ℝ)|^5711 ≤ (8156293257311/25000000000000 : ℝ)^4687
        have hw : |(997043987/2500000000 : ℝ)|=(997043987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5093929519/10000000000 : ℝ)|^5711 ≤ (1758372295613/4000000000000 : ℝ)^4687
        have hw : |(5093929519/10000000000 : ℝ)|=(5093929519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3037761837/10000000000 : ℝ)|^5711 ≤ (11707759785847/50000000000000 : ℝ)^4687
        have hw : |(3037761837/10000000000 : ℝ)|=(3037761837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1746_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (41/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21053/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5695/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5695 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5695*1^1024 ≤ 0^1024*1^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5695/1024 : ℝ) ≤ (306067572741992179/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5695 ≤ (306067572741992179/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5695*50000000000000000000^1024 ≤ 306067572741992179^1024*5^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 306067572741992179 50000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (306067572741992179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5695 := by
      have hnat : (1 : ℕ)^1024*1^5695 ≤ 1^5695*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50306067572741992179/50000000000000000000 : ℝ) ≤ (10010979080902507/10000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (50306067572741992179/50000000000000000000 : ℝ)^1024 ≤ (10010979080902507/10000000000000000 : ℝ)^5695 := by
      have hnat : (50306067572741992179 : ℕ)^1024*10000000000000000^5695 ≤ 10010979080902507^5695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50306067572741992179 50000000000000000000 10010979080902507 10000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010979080902507/10000000000000000 : ℝ)) (X := (50306067572741992179/50000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25306067572741992179/25000000000000000000 : ℝ) ≤ (5010979080902507/5000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (25306067572741992179/25000000000000000000 : ℝ)^1024 ≤ (5010979080902507/5000000000000000 : ℝ)^5695 := by
      have hnat : (25306067572741992179 : ℕ)^1024*5000000000000000^5695 ≤ 5010979080902507^5695*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25306067572741992179 25000000000000000000 5010979080902507 5000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010979080902507/5000000000000000 : ℝ)) (X := (25306067572741992179/25000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10979080902507/4000000000000000 : ℝ)*(0 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10979080902507/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(306067572741992179/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10979080902507/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5695/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10979080902507/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10010979080902507/10000000000000000 : ℝ) by norm_num, show 1+(306067572741992179/50000000000000000000 : ℝ)+(0 : ℝ)=(50306067572741992179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(306067572741992179/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10979080902507/4000000000000000 : ℝ)*(2/5 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10979080902507/4000000000000000 : ℝ)*(2/5 : ℝ)=(5010979080902507/5000000000000000 : ℝ) by norm_num, show 1+2*(306067572741992179/50000000000000000000 : ℝ)=(25306067572741992179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10979080902507/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10979080902507/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10979080902507/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10979080902507/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10979080902507/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10979080902507/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1196579433/10000000000 : ℝ)*X 0 0+(352680397/625000000 : ℝ)*X 0 1+(4971699359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376519937/10000000000 : ℝ)*X 1 0+(-778683699/5000000000 : ℝ)*X 1 1+(310731229/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376521001/10000000000 : ℝ)*X 2 0+(4971699047/10000000000 : ℝ)*X 2 1+(-778683399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((796696891/2000000000 : ℝ)*X 0 0+(2980279427/10000000000 : ℝ)*X 0 1+(5149547089/10000000000 : ℝ)*X 0 2+(796696891/2000000000 : ℝ)*X 1 0+(2980279427/10000000000 : ℝ)*X 1 1+(5149547089/10000000000 : ℝ)*X 1 2+(796696891/2000000000 : ℝ)*X 2 0+(2980279427/10000000000 : ℝ)*X 2 1+(5149547089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-29950773/250000000 : ℝ)*X 0 0+(1247226901/2500000000 : ℝ)*X 0 1+(2812550381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5197101549/10000000000 : ℝ)*X 1 0+(-451982703/5000000000 : ℝ)*X 1 1+(2812550437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039420253/2000000000 : ℝ)*X 2 0+(5625100833/10000000000 : ℝ)*X 2 1+(-903965883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((997043987/2500000000 : ℝ)*X 0 0+(5093929519/10000000000 : ℝ)*X 0 1+(3037761837/10000000000 : ℝ)*X 0 2+(997043987/2500000000 : ℝ)*X 1 0+(5093929519/10000000000 : ℝ)*X 1 1+(3037761837/10000000000 : ℝ)*X 1 2+(997043987/2500000000 : ℝ)*X 2 0+(5093929519/10000000000 : ℝ)*X 2 1+(3037761837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209329417095166697400723/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357867879/50000000000000 : ℝ)*(base19) + (37562877/4000000000000 : ℝ)*(base23) + (745643/10000000000000 : ℝ)*(base24) + (34439841/100000000000000 : ℝ)*(upper4) + (24720429/10000000000000 : ℝ)*(upper5) + (243861821233679/25000000000000 : ℝ)*(major0) + (243861821233679/25000000000000 : ℝ)*(major1) + (243861821233679/25000000000000 : ℝ)*(major2) + (372475052276751/25000000000000 : ℝ)*(sp0) + (1489905696840947/100000000000000 : ℝ)*(sp1) + (1489905466048351/100000000000000 : ℝ)*(sp2) + (92197361858429/20000000000000 : ℝ)*(sp3) + (6203469701/100000000000000 : ℝ)*(sp4) + (120844763/10000000000000 : ℝ)*(sp7) + (225091805537/48828125000 : ℝ)*(f.failure) + (297981282515341/20000000000000 : ℝ)*(f.sum) + (352086185783253/50000000000000000000000000000 : ℝ)*base65 + (433080794233253/100000000000000000000000000000 : ℝ)*base67 + (86067982633253/100000000000000000000000000000 : ℝ)*base69 + (1160314508533253/100000000000000000000000000000 : ℝ)*base71 + (43654214983253/50000000000000000000000000000 : ℝ)*base73 + (131243938366747/100000000000000000000000000000 : ℝ)*base76 + (56631392666747/100000000000000000000000000000 : ℝ)*base78 + (171009774266747/100000000000000000000000000000 : ℝ)*base80 + (373513358083253/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (67679/9765625000000000000 : ℝ)*base89 + (67679/9765625000000000000 : ℝ)*base91 + (67679/9765625000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (441433883211283528945047/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1049099293/100000000000000 : ℝ)*(base19) + (243262887/25000000000000 : ℝ)*(base23) + (20982779/100000000000000 : ℝ)*(upper2) + (36581797/20000000000000 : ℝ)*(upper3) + (31781281/20000000000000 : ℝ)*(upper5) + (1029095402601469/100000000000000 : ℝ)*(major0) + (1029095402601469/100000000000000 : ℝ)*(major1) + (1029095402601469/100000000000000 : ℝ)*(major2) + (4494422073/100000000000000 : ℝ)*(sp1) + (225634027/6250000000000 : ℝ)*(sp2) + (1571849000198119/100000000000000 : ℝ)*(sp4) + (1571843456676753/100000000000000 : ℝ)*(sp5) + (1571844417002139/100000000000000 : ℝ)*(sp6) + (486341657860187/100000000000000 : ℝ)*(sp7) + (486341657860187/100000000000000 : ℝ)*(f.failure) + (1571849000198119/100000000000000 : ℝ)*(f.sum) + (509684395217217/200000000000000000000000000000 : ℝ)*base66 + (1387118607617217/400000000000000000000000000000 : ℝ)*base68 + (2254475914817217/400000000000000000000000000000 : ℝ)*base70 + (909672665617217/400000000000000000000000000000 : ℝ)*base72 + (690411292217217/200000000000000000000000000000 : ℝ)*base74 + (1176955481217217/400000000000000000000000000000 : ℝ)*base76 + (1393617653217217/400000000000000000000000000000 : ℝ)*base78 + (1456255093617217/400000000000000000000000000000 : ℝ)*base80 + (1254194045217217/200000000000000000000000000000 : ℝ)*base82 + (89123677/10000000000000000000000 : ℝ)*base89 + (89123677/10000000000000000000000 : ℝ)*base91 + (89123677/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1746_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (41/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1746_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1746_s1_0 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1243585469/10000000000 : ℝ)*x 0 + (1101290753/2000000000 : ℝ)*x 1 + (2538381509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1243585469/10000000000 : ℝ)^5711 ≤ (7886483816849/100000000000000 : ℝ)^4687 := by
    have hnat : (1243585469 : ℕ)^5711*100000000000000^4687 ≤ 7886483816849^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243585469 10000000000 7886483816849 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101290753/2000000000 : ℝ)^5711 ≤ (48334650456941/100000000000000 : ℝ)^4687 := by
    have hnat : (1101290753 : ℕ)^5711*100000000000000^4687 ≤ 48334650456941^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101290753 2000000000 48334650456941 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538381509/5000000000 : ℝ)^5711 ≤ (43778865714673/100000000000000 : ℝ)^4687 := by
    have hnat : (2538381509 : ℕ)^5711*100000000000000^4687 ≤ 43778865714673^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538381509 5000000000 43778865714673 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1243585469/10000000000 : ℝ), (1101290753/2000000000 : ℝ), (2538381509/5000000000 : ℝ)] ![(7886483816849/100000000000000 : ℝ), (48334650456941/100000000000000 : ℝ), (43778865714673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1243585469/10000000000 : ℝ)|^5711 ≤ (7886483816849/100000000000000 : ℝ)^4687
        have hw : |(-1243585469/10000000000 : ℝ)|=(1243585469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101290753/2000000000 : ℝ)|^5711 ≤ (48334650456941/100000000000000 : ℝ)^4687
        have hw : |(1101290753/2000000000 : ℝ)|=(1101290753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538381509/5000000000 : ℝ)|^5711 ≤ (43778865714673/100000000000000 : ℝ)^4687
        have hw : |(2538381509/5000000000 : ℝ)|=(2538381509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_1 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213607691/400000000 : ℝ)*x 0 + (-1468692363/10000000000 : ℝ)*x 1 + (2538381457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213607691/400000000 : ℝ)^5711 ≤ (46562301700833/100000000000000 : ℝ)^4687 := by
    have hnat : (213607691 : ℕ)^5711*100000000000000^4687 ≤ 46562301700833^4687*400000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213607691 400000000 46562301700833 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1468692363/10000000000 : ℝ)^5711 ≤ (4829416830703/50000000000000 : ℝ)^4687 := by
    have hnat : (1468692363 : ℕ)^5711*50000000000000^4687 ≤ 4829416830703^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468692363 10000000000 4829416830703 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538381457/5000000000 : ℝ)^5711 ≤ (2736179038869/6250000000000 : ℝ)^4687 := by
    have hnat : (2538381457 : ℕ)^5711*6250000000000^4687 ≤ 2736179038869^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538381457 5000000000 2736179038869 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213607691/400000000 : ℝ), (-1468692363/10000000000 : ℝ), (2538381457/5000000000 : ℝ)] ![(46562301700833/100000000000000 : ℝ), (4829416830703/50000000000000 : ℝ), (2736179038869/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213607691/400000000 : ℝ)|^5711 ≤ (46562301700833/100000000000000 : ℝ)^4687
        have hw : |(213607691/400000000 : ℝ)|=(213607691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1468692363/10000000000 : ℝ)|^5711 ≤ (4829416830703/50000000000000 : ℝ)^4687
        have hw : |(-1468692363/10000000000 : ℝ)|=(1468692363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538381457/5000000000 : ℝ)|^5711 ≤ (2736179038869/6250000000000 : ℝ)^4687
        have hw : |(2538381457/5000000000 : ℝ)|=(2538381457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_2 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340191853/10000000000 : ℝ)*x 0 + (2538381597/5000000000 : ℝ)*x 1 + (-367173139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340191853/10000000000 : ℝ)^5711 ≤ (9312459443487/20000000000000 : ℝ)^4687 := by
    have hnat : (5340191853 : ℕ)^5711*20000000000000^4687 ≤ 9312459443487^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340191853 10000000000 9312459443487 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538381597/5000000000 : ℝ)^5711 ≤ (43778867563973/100000000000000 : ℝ)^4687 := by
    have hnat : (2538381597 : ℕ)^5711*100000000000000^4687 ≤ 43778867563973^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538381597 5000000000 43778867563973 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367173139/2500000000 : ℝ)^5711 ≤ (2414708801993/25000000000000 : ℝ)^4687 := by
    have hnat : (367173139 : ℕ)^5711*25000000000000^4687 ≤ 2414708801993^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367173139 2500000000 2414708801993 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340191853/10000000000 : ℝ), (2538381597/5000000000 : ℝ), (-367173139/2500000000 : ℝ)] ![(9312459443487/20000000000000 : ℝ), (43778867563973/100000000000000 : ℝ), (2414708801993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340191853/10000000000 : ℝ)|^5711 ≤ (9312459443487/20000000000000 : ℝ)^4687
        have hw : |(5340191853/10000000000 : ℝ)|=(5340191853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538381597/5000000000 : ℝ)|^5711 ≤ (43778867563973/100000000000000 : ℝ)^4687
        have hw : |(2538381597/5000000000 : ℝ)|=(2538381597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367173139/2500000000 : ℝ)|^5711 ≤ (2414708801993/25000000000000 : ℝ)^4687
        have hw : |(-367173139/2500000000 : ℝ)|=(367173139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_3 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2014144501/5000000000 : ℝ)*x 0 + (3367077891/10000000000 : ℝ)*x 1 + (951166227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014144501/5000000000 : ℝ)^5711 ≤ (33025446779793/100000000000000 : ℝ)^4687 := by
    have hnat : (2014144501 : ℕ)^5711*100000000000000^4687 ≤ 33025446779793^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014144501 5000000000 33025446779793 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3367077891/10000000000 : ℝ)^5711 ≤ (13272081139473/50000000000000 : ℝ)^4687 := by
    have hnat : (3367077891 : ℕ)^5711*50000000000000^4687 ≤ 13272081139473^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3367077891 10000000000 13272081139473 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (951166227/2000000000 : ℝ)^5711 ≤ (40430390924067/100000000000000 : ℝ)^4687 := by
    have hnat : (951166227 : ℕ)^5711*100000000000000^4687 ≤ 40430390924067^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951166227 2000000000 40430390924067 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2014144501/5000000000 : ℝ), (3367077891/10000000000 : ℝ), (951166227/2000000000 : ℝ)] ![(33025446779793/100000000000000 : ℝ), (13272081139473/50000000000000 : ℝ), (40430390924067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2014144501/5000000000 : ℝ)|^5711 ≤ (33025446779793/100000000000000 : ℝ)^4687
        have hw : |(2014144501/5000000000 : ℝ)|=(2014144501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3367077891/10000000000 : ℝ)|^5711 ≤ (13272081139473/50000000000000 : ℝ)^4687
        have hw : |(3367077891/10000000000 : ℝ)|=(3367077891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(951166227/2000000000 : ℝ)|^5711 ≤ (40430390924067/100000000000000 : ℝ)^4687
        have hw : |(951166227/2000000000 : ℝ)|=(951166227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_4 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1243963393/10000000000 : ℝ)*x 0 + (2541911697/5000000000 : ℝ)*x 1 + (219969699/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1243963393/10000000000 : ℝ)^5711 ≤ (197235105679/2500000000000 : ℝ)^4687 := by
    have hnat : (1243963393 : ℕ)^5711*2500000000000^4687 ≤ 197235105679^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243963393 10000000000 197235105679 2500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541911697/5000000000 : ℝ)^5711 ≤ (43853063099759/100000000000000 : ℝ)^4687 := by
    have hnat : (2541911697 : ℕ)^5711*100000000000000^4687 ≤ 43853063099759^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541911697 5000000000 43853063099759 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219969699/400000000 : ℝ)^5711 ≤ (6032191582879/12500000000000 : ℝ)^4687 := by
    have hnat : (219969699 : ℕ)^5711*12500000000000^4687 ≤ 6032191582879^4687*400000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219969699 400000000 6032191582879 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1243963393/10000000000 : ℝ), (2541911697/5000000000 : ℝ), (219969699/400000000 : ℝ)] ![(197235105679/2500000000000 : ℝ), (43853063099759/100000000000000 : ℝ), (6032191582879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1243963393/10000000000 : ℝ)|^5711 ≤ (197235105679/2500000000000 : ℝ)^4687
        have hw : |(-1243963393/10000000000 : ℝ)|=(1243963393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541911697/5000000000 : ℝ)|^5711 ≤ (43853063099759/100000000000000 : ℝ)^4687
        have hw : |(2541911697/5000000000 : ℝ)|=(2541911697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219969699/400000000 : ℝ)|^5711 ≤ (6032191582879/12500000000000 : ℝ)^4687
        have hw : |(219969699/400000000 : ℝ)|=(219969699/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_5 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306536759/2500000000 : ℝ)*x 0 + (-1046212747/10000000000 : ℝ)*x 1 + (34370267/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306536759/2500000000 : ℝ)^5711 ≤ (22676754455117/50000000000000 : ℝ)^4687 := by
    have hnat : (1306536759 : ℕ)^5711*50000000000000^4687 ≤ 22676754455117^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306536759 2500000000 22676754455117 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046212747/10000000000 : ℝ)^5711 ≤ (399309736777/6250000000000 : ℝ)^4687 := by
    have hnat : (1046212747 : ℕ)^5711*6250000000000^4687 ≤ 399309736777^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046212747 10000000000 399309736777 6250000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34370267/62500000 : ℝ)^5711 ≤ (6032191910337/12500000000000 : ℝ)^4687 := by
    have hnat : (34370267 : ℕ)^5711*12500000000000^4687 ≤ 6032191910337^4687*62500000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34370267 62500000 6032191910337 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306536759/2500000000 : ℝ), (-1046212747/10000000000 : ℝ), (34370267/62500000 : ℝ)] ![(22676754455117/50000000000000 : ℝ), (399309736777/6250000000000 : ℝ), (6032191910337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306536759/2500000000 : ℝ)|^5711 ≤ (22676754455117/50000000000000 : ℝ)^4687
        have hw : |(1306536759/2500000000 : ℝ)|=(1306536759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046212747/10000000000 : ℝ)|^5711 ≤ (399309736777/6250000000000 : ℝ)^4687
        have hw : |(-1046212747/10000000000 : ℝ)|=(1046212747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34370267/62500000 : ℝ)|^5711 ≤ (6032191910337/12500000000000 : ℝ)^4687
        have hw : |(34370267/62500000 : ℝ)|=(34370267/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_6 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226146867/10000000000 : ℝ)*x 0 + (1374810713/2500000000 : ℝ)*x 1 + (-1046212797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226146867/10000000000 : ℝ)^5711 ≤ (22676753561599/50000000000000 : ℝ)^4687 := by
    have hnat : (5226146867 : ℕ)^5711*50000000000000^4687 ≤ 22676753561599^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226146867 10000000000 22676753561599 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374810713/2500000000 : ℝ)^5711 ≤ (24128768347053/50000000000000 : ℝ)^4687 := by
    have hnat : (1374810713 : ℕ)^5711*50000000000000^4687 ≤ 24128768347053^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374810713 2500000000 24128768347053 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046212797/10000000000 : ℝ)^5711 ≤ (3194478080239/50000000000000 : ℝ)^4687 := by
    have hnat : (1046212797 : ℕ)^5711*50000000000000^4687 ≤ 3194478080239^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046212797 10000000000 3194478080239 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226146867/10000000000 : ℝ), (1374810713/2500000000 : ℝ), (-1046212797/10000000000 : ℝ)] ![(22676753561599/50000000000000 : ℝ), (24128768347053/50000000000000 : ℝ), (3194478080239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226146867/10000000000 : ℝ)|^5711 ≤ (22676753561599/50000000000000 : ℝ)^4687
        have hw : |(5226146867/10000000000 : ℝ)|=(5226146867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374810713/2500000000 : ℝ)|^5711 ≤ (24128768347053/50000000000000 : ℝ)^4687
        have hw : |(1374810713/2500000000 : ℝ)|=(1374810713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046212797/10000000000 : ℝ)|^5711 ≤ (3194478080239/50000000000000 : ℝ)^4687
        have hw : |(-1046212797/10000000000 : ℝ)|=(1046212797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s1_7 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4029510439/10000000000 : ℝ)*x 0 + (473301321/1000000000 : ℝ)*x 1 + (3390383159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4029510439/10000000000 : ℝ)^5711 ≤ (33037648771987/100000000000000 : ℝ)^4687 := by
    have hnat : (4029510439 : ℕ)^5711*100000000000000^4687 ≤ 33037648771987^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029510439 10000000000 33037648771987 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473301321/1000000000 : ℝ)^5711 ≤ (40194154475233/100000000000000 : ℝ)^4687 := by
    have hnat : (473301321 : ℕ)^5711*100000000000000^4687 ≤ 40194154475233^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473301321 1000000000 40194154475233 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3390383159/10000000000 : ℝ)^5711 ≤ (13384098368889/50000000000000 : ℝ)^4687 := by
    have hnat : (3390383159 : ℕ)^5711*50000000000000^4687 ≤ 13384098368889^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3390383159 10000000000 13384098368889 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4029510439/10000000000 : ℝ), (473301321/1000000000 : ℝ), (3390383159/10000000000 : ℝ)] ![(33037648771987/100000000000000 : ℝ), (40194154475233/100000000000000 : ℝ), (13384098368889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4029510439/10000000000 : ℝ)|^5711 ≤ (33037648771987/100000000000000 : ℝ)^4687
        have hw : |(4029510439/10000000000 : ℝ)|=(4029510439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(473301321/1000000000 : ℝ)|^5711 ≤ (40194154475233/100000000000000 : ℝ)^4687
        have hw : |(473301321/1000000000 : ℝ)|=(473301321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3390383159/10000000000 : ℝ)|^5711 ≤ (13384098368889/50000000000000 : ℝ)^4687
        have hw : |(3390383159/10000000000 : ℝ)|=(3390383159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1746_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (41/625 : ℝ)*pair X i i ≤ pair X i h) :
    (4459/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9069/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (41/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (41/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (41/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (41/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (41/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (41/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (41/625 : ℝ) ^ (5695/1024 : ℝ) ≤ (6578440978073/25000000000000000000 : ℝ) := by
    have hpowers : (41/625 : ℝ)^5695 ≤ (6578440978073/25000000000000000000 : ℝ)^1024 := by
      have hnat : (41 : ℕ)^5695*25000000000000000000^1024 ≤ 6578440978073^1024*625^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41 625 6578440978073 25000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41/625 : ℝ)) (X := (6578440978073/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21053/100000 : ℝ) ^ (5695/1024 : ℝ) ≤ (3448457625696193/20000000000000000000 : ℝ) := by
    have hpowers : (21053/100000 : ℝ)^5695 ≤ (3448457625696193/20000000000000000000 : ℝ)^1024 := by
      have hnat : (21053 : ℕ)^5695*20000000000000000000^1024 ≤ 3448457625696193^1024*100000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21053 100000 3448457625696193 20000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21053/100000 : ℝ)) (X := (3448457625696193/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500006578440978073/12500000000000000000 : ℝ) ≤ (5000000473139393/5000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (12500006578440978073/12500000000000000000 : ℝ)^1024 ≤ (5000000473139393/5000000000000000 : ℝ)^5695 := by
      have hnat : (12500006578440978073 : ℕ)^1024*5000000000000000^5695 ≤ 5000000473139393^5695*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500006578440978073 12500000000000000000 5000000473139393 5000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000473139393/5000000000000000 : ℝ)) (X := (12500006578440978073/12500000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017268601892393257/100000000000000000000 : ℝ) ≤ (10000310479300999/10000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (100017268601892393257/100000000000000000000 : ℝ)^1024 ≤ (10000310479300999/10000000000000000 : ℝ)^5695 := by
      have hnat : (100017268601892393257 : ℕ)^1024*10000000000000000^5695 ≤ 10000310479300999^5695*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017268601892393257 100000000000000000000 10000310479300999 10000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000310479300999/10000000000000000 : ℝ)) (X := (100017268601892393257/100000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003448457625696193/10000000000000000000 : ℝ) ≤ (2500155003080803/2500000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (10003448457625696193/10000000000000000000 : ℝ)^1024 ≤ (2500155003080803/2500000000000000 : ℝ)^5695 := by
      have hnat : (10003448457625696193 : ℕ)^1024*2500000000000000^5695 ≤ 2500155003080803^5695*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003448457625696193 10000000000000000000 2500155003080803 2500000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500155003080803/2500000000000000 : ℝ)) (X := (10003448457625696193/10000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6578440978073/25000000000000000000 : ℝ) ≤ ((24154325440194501823/24155000000000000000 : ℝ)+2*(103177674071/483100000000000 : ℝ)*(41/625 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (24154325440194501823/24155000000000000000 : ℝ)+2*(103177674071/483100000000000 : ℝ)*(41/625 : ℝ)=(5000000473139393/5000000000000000 : ℝ) by norm_num, show 1+2*(6578440978073/25000000000000000000 : ℝ)=(12500006578440978073/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3448457625696193/20000000000000000000 : ℝ)+(6578440978073/25000000000000000000 : ℝ) ≤ ((24154325440194501823/24155000000000000000 : ℝ)+(103177674071/483100000000000 : ℝ)*((21053/100000 : ℝ)+(41/625 : ℝ)))^(5695/1024 : ℝ) := by
    rw [show (24154325440194501823/24155000000000000000 : ℝ)+(103177674071/483100000000000 : ℝ)*((21053/100000 : ℝ)+(41/625 : ℝ))=(10000310479300999/10000000000000000 : ℝ) by norm_num, show 1+(3448457625696193/20000000000000000000 : ℝ)+(6578440978073/25000000000000000000 : ℝ)=(100017268601892393257/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3448457625696193/20000000000000000000 : ℝ) ≤ ((24154325440194501823/24155000000000000000 : ℝ)+2*(103177674071/483100000000000 : ℝ)*(21053/100000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (24154325440194501823/24155000000000000000 : ℝ)+2*(103177674071/483100000000000 : ℝ)*(21053/100000 : ℝ)=(2500155003080803/2500000000000000 : ℝ) by norm_num, show 1+2*(3448457625696193/20000000000000000000 : ℝ)=(10003448457625696193/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24154325440194501823/24155000000000000000 : ℝ)*(X 1 0+X 2 0)+(103177674071/483100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (41/625 : ℝ)) (hi := (21053/100000 : ℝ)) (c := (24154325440194501823/24155000000000000000 : ℝ)) (alpha := (103177674071/483100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24154325440194501823/24155000000000000000 : ℝ)*(X 0 1+X 2 1)+(103177674071/483100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (41/625 : ℝ)) (hi := (21053/100000 : ℝ)) (c := (24154325440194501823/24155000000000000000 : ℝ)) (alpha := (103177674071/483100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24154325440194501823/24155000000000000000 : ℝ)*(X 0 2+X 1 2)+(103177674071/483100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (41/625 : ℝ)) (hi := (21053/100000 : ℝ)) (c := (24154325440194501823/24155000000000000000 : ℝ)) (alpha := (103177674071/483100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1243585469/10000000000 : ℝ)*X 0 0+(1101290753/2000000000 : ℝ)*X 0 1+(2538381509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213607691/400000000 : ℝ)*X 1 0+(-1468692363/10000000000 : ℝ)*X 1 1+(2538381457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5340191853/10000000000 : ℝ)*X 2 0+(2538381597/5000000000 : ℝ)*X 2 1+(-367173139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2014144501/5000000000 : ℝ)*X 0 0+(3367077891/10000000000 : ℝ)*X 0 1+(951166227/2000000000 : ℝ)*X 0 2+(2014144501/5000000000 : ℝ)*X 1 0+(3367077891/10000000000 : ℝ)*X 1 1+(951166227/2000000000 : ℝ)*X 1 2+(2014144501/5000000000 : ℝ)*X 2 0+(3367077891/10000000000 : ℝ)*X 2 1+(951166227/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1243963393/10000000000 : ℝ)*X 0 0+(2541911697/5000000000 : ℝ)*X 0 1+(219969699/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1306536759/2500000000 : ℝ)*X 1 0+(-1046212747/10000000000 : ℝ)*X 1 1+(34370267/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5226146867/10000000000 : ℝ)*X 2 0+(1374810713/2500000000 : ℝ)*X 2 1+(-1046212797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4029510439/10000000000 : ℝ)*X 0 0+(473301321/1000000000 : ℝ)*X 0 1+(3390383159/10000000000 : ℝ)*X 0 2+(4029510439/10000000000 : ℝ)*X 1 0+(473301321/1000000000 : ℝ)*X 1 1+(3390383159/10000000000 : ℝ)*X 1 2+(4029510439/10000000000 : ℝ)*X 2 0+(473301321/1000000000 : ℝ)*X 2 1+(3390383159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7692903230166811035064917771/1207750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24516901/2500000000000 : ℝ)*(base19) + (341856073/50000000000000 : ℝ)*(base23) + (15093423/25000000000000 : ℝ)*(lower2) + (109217351/50000000000000 : ℝ)*(upper3) + (8661723/100000000000000 : ℝ)*(upper5) + (1523671898227347/100000000000000 : ℝ)*(major0) + (1523671898227347/100000000000000 : ℝ)*(major1) + (1523671898227347/100000000000000 : ℝ)*(major2) + (1163631816491087/50000000000000 : ℝ)*(sp0) + (2327268337121289/100000000000000 : ℝ)*(sp1) + (1163634317042591/50000000000000 : ℝ)*(sp2) + (720071818597423/100000000000000 : ℝ)*(sp3) + (2842407577/50000000000000 : ℝ)*(sp4) + (1223869707/50000000000000 : ℝ)*(sp7) + (360037133168419/50000000000000 : ℝ)*(f.failure) + (2327269317797329/100000000000000 : ℝ)*(f.sum) + (61287234223283/24155000000000000000000000000 : ℝ)*base66 + (15397329144747303581/2415500000000000000000000000000000 : ℝ)*base67 + (15517452940440303581/2415500000000000000000000000000000 : ℝ)*base69 + (13363489140103303581/2415500000000000000000000000000000 : ℝ)*base71 + (52166800482893/24155000000000000000000000000 : ℝ)*base74 + (787326049448303581/2415500000000000000000000000000000 : ℝ)*base75 + (4260484703252803581/2415500000000000000000000000000000 : ℝ)*base77 + (27070731642356303581/2415500000000000000000000000000000 : ℝ)*base79 + (3098721992727/6038750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (30622549/5000000000000000000000 : ℝ)*base89 + (30622549/5000000000000000000000 : ℝ)*base91 + (30622549/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6591788064666032631912233907/603875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289323543/20000000000000 : ℝ)*(base19) + (1564123109/100000000000000 : ℝ)*(base23) + (35899303/12500000000000 : ℝ)*(upper3) + (622869/781250000000 : ℝ)*(lower4) + (178245371/100000000000000 : ℝ)*(upper5) + (788003093672499/50000000000000 : ℝ)*(major0) + (788003093672499/50000000000000 : ℝ)*(major1) + (788003093672499/50000000000000 : ℝ)*(major2) + (500461341/5000000000000 : ℝ)*(sp1) + (2394055597/20000000000000 : ℝ)*(sp2) + (1203602504236087/50000000000000 : ℝ)*(sp4) + (1203596776313819/50000000000000 : ℝ)*(sp5) + (60179786851777/2500000000000 : ℝ)*(sp6) + (744807002357299/100000000000000 : ℝ)*(sp7) + (744807002357299/100000000000000 : ℝ)*(f.failure) + (1203602504236087/50000000000000 : ℝ)*(f.sum) + (95713801720387/24155000000000000000000000000 : ℝ)*base66 + (7175283462110415677/1207750000000000000000000000000000 : ℝ)*base67 + (250697334311665677/1207750000000000000000000000000000 : ℝ)*base69 + (1955892339042165677/1207750000000000000000000000000000 : ℝ)*base71 + (43873829248269/12077500000000000000000000000 : ℝ)*base73 + (13999653055339165677/1207750000000000000000000000000000 : ℝ)*base75 + (5715175935390415677/1207750000000000000000000000000000 : ℝ)*base77 + (7359869095181915677/1207750000000000000000000000000000 : ℝ)*base79 + (42894528010897/24155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (50070971/10000000000000000000000 : ℝ)*base90 + (50070971/10000000000000000000000 : ℝ)*base92 + (50070971/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1746_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (41/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9069/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1746_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1746_s2_0 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1244805847/10000000000 : ℝ)*x 0 + (550254401/1000000000 : ℝ)*x 1 + (158745147/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1244805847/10000000000 : ℝ)^5711 ≤ (3947957496931/50000000000000 : ℝ)^4687 := by
    have hnat : (1244805847 : ℕ)^5711*50000000000000^4687 ≤ 3947957496931^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244805847 10000000000 3947957496931 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550254401/1000000000 : ℝ)^5711 ≤ (48292836656421/100000000000000 : ℝ)^4687 := by
    have hnat : (550254401 : ℕ)^5711*100000000000000^4687 ≤ 48292836656421^4687*1000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550254401 1000000000 48292836656421 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158745147/312500000 : ℝ)^5711 ≤ (1369101510493/3125000000000 : ℝ)^4687 := by
    have hnat : (158745147 : ℕ)^5711*3125000000000^4687 ≤ 1369101510493^4687*312500000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158745147 312500000 1369101510493 3125000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1244805847/10000000000 : ℝ), (550254401/1000000000 : ℝ), (158745147/312500000 : ℝ)] ![(3947957496931/50000000000000 : ℝ), (48292836656421/100000000000000 : ℝ), (1369101510493/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1244805847/10000000000 : ℝ)|^5711 ≤ (3947957496931/50000000000000 : ℝ)^4687
        have hw : |(-1244805847/10000000000 : ℝ)|=(1244805847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550254401/1000000000 : ℝ)|^5711 ≤ (48292836656421/100000000000000 : ℝ)^4687
        have hw : |(550254401/1000000000 : ℝ)|=(550254401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158745147/312500000 : ℝ)|^5711 ≤ (1369101510493/3125000000000 : ℝ)^4687
        have hw : |(158745147/312500000 : ℝ)|=(158745147/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_1 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334777629/2500000000 : ℝ)*x 0 + (-916303/6250000 : ℝ)*x 1 + (5079844697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334777629/2500000000 : ℝ)^5711 ≤ (11637702292621/25000000000000 : ℝ)^4687 := by
    have hnat : (1334777629 : ℕ)^5711*25000000000000^4687 ≤ 11637702292621^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334777629 2500000000 11637702292621 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916303/6250000 : ℝ)^5711 ≤ (2409485636953/25000000000000 : ℝ)^4687 := by
    have hnat : (916303 : ℕ)^5711*25000000000000^4687 ≤ 2409485636953^4687*6250000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916303 6250000 2409485636953 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079844697/10000000000 : ℝ)^5711 ≤ (21905624131107/50000000000000 : ℝ)^4687 := by
    have hnat : (5079844697 : ℕ)^5711*50000000000000^4687 ≤ 21905624131107^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079844697 10000000000 21905624131107 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334777629/2500000000 : ℝ), (-916303/6250000 : ℝ), (5079844697/10000000000 : ℝ)] ![(11637702292621/25000000000000 : ℝ), (2409485636953/25000000000000 : ℝ), (21905624131107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334777629/2500000000 : ℝ)|^5711 ≤ (11637702292621/25000000000000 : ℝ)^4687
        have hw : |(1334777629/2500000000 : ℝ)|=(1334777629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-916303/6250000 : ℝ)|^5711 ≤ (2409485636953/25000000000000 : ℝ)^4687
        have hw : |(-916303/6250000 : ℝ)|=(916303/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079844697/10000000000 : ℝ)|^5711 ≤ (21905624131107/50000000000000 : ℝ)^4687
        have hw : |(5079844697/10000000000 : ℝ)|=(5079844697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_2 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33369441/62500000 : ℝ)*x 0 + (2539922357/5000000000 : ℝ)*x 1 + (-18326059/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33369441/62500000 : ℝ)^5711 ≤ (23275404818963/50000000000000 : ℝ)^4687 := by
    have hnat : (33369441 : ℕ)^5711*50000000000000^4687 ≤ 23275404818963^4687*62500000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33369441 62500000 23275404818963 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539922357/5000000000 : ℝ)^5711 ≤ (1369101513777/3125000000000 : ℝ)^4687 := by
    have hnat : (2539922357 : ℕ)^5711*3125000000000^4687 ≤ 1369101513777^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539922357 5000000000 1369101513777 3125000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18326059/125000000 : ℝ)^5711 ≤ (4818970953499/50000000000000 : ℝ)^4687 := by
    have hnat : (18326059 : ℕ)^5711*50000000000000^4687 ≤ 4818970953499^4687*125000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18326059 125000000 4818970953499 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33369441/62500000 : ℝ), (2539922357/5000000000 : ℝ), (-18326059/125000000 : ℝ)] ![(23275404818963/50000000000000 : ℝ), (1369101513777/3125000000000 : ℝ), (4818970953499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33369441/62500000 : ℝ)|^5711 ≤ (23275404818963/50000000000000 : ℝ)^4687
        have hw : |(33369441/62500000 : ℝ)|=(33369441/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539922357/5000000000 : ℝ)|^5711 ≤ (1369101513777/3125000000000 : ℝ)^4687
        have hw : |(2539922357/5000000000 : ℝ)|=(2539922357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18326059/125000000 : ℝ)|^5711 ≤ (4818970953499/50000000000000 : ℝ)^4687
        have hw : |(-18326059/125000000 : ℝ)|=(18326059/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_3 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2014643189/5000000000 : ℝ)*x 0 + (675659789/2000000000 : ℝ)*x 1 + (4744456883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014643189/5000000000 : ℝ)^5711 ≤ (33035410372049/100000000000000 : ℝ)^4687 := by
    have hnat : (2014643189 : ℕ)^5711*100000000000000^4687 ≤ 33035410372049^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014643189 5000000000 33035410372049 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675659789/2000000000 : ℝ)^5711 ≤ (26651988567503/100000000000000 : ℝ)^4687 := by
    have hnat : (675659789 : ℕ)^5711*100000000000000^4687 ≤ 26651988567503^4687*2000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675659789 2000000000 26651988567503 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4744456883/10000000000 : ℝ)^5711 ≤ (40312601033467/100000000000000 : ℝ)^4687 := by
    have hnat : (4744456883 : ℕ)^5711*100000000000000^4687 ≤ 40312601033467^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4744456883 10000000000 40312601033467 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2014643189/5000000000 : ℝ), (675659789/2000000000 : ℝ), (4744456883/10000000000 : ℝ)] ![(33035410372049/100000000000000 : ℝ), (26651988567503/100000000000000 : ℝ), (40312601033467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2014643189/5000000000 : ℝ)|^5711 ≤ (33035410372049/100000000000000 : ℝ)^4687
        have hw : |(2014643189/5000000000 : ℝ)|=(2014643189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675659789/2000000000 : ℝ)|^5711 ≤ (26651988567503/100000000000000 : ℝ)^4687
        have hw : |(675659789/2000000000 : ℝ)|=(675659789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4744456883/10000000000 : ℝ)|^5711 ≤ (40312601033467/100000000000000 : ℝ)^4687
        have hw : |(4744456883/10000000000 : ℝ)|=(4744456883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_4 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1245165371/10000000000 : ℝ)*x 0 + (635834617/1250000000 : ℝ)*x 1 + (5495568249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1245165371/10000000000 : ℝ)^5711 ≤ (789869380889/10000000000000 : ℝ)^4687 := by
    have hnat : (1245165371 : ℕ)^5711*10000000000000^4687 ≤ 789869380889^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245165371 10000000000 789869380889 10000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635834617/1250000000 : ℝ)^5711 ≤ (4388305732017/10000000000000 : ℝ)^4687 := by
    have hnat : (635834617 : ℕ)^5711*10000000000000^4687 ≤ 4388305732017^4687*1250000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635834617 1250000000 4388305732017 10000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495568249/10000000000 : ℝ)^5711 ≤ (24109124426021/50000000000000 : ℝ)^4687 := by
    have hnat : (5495568249 : ℕ)^5711*50000000000000^4687 ≤ 24109124426021^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495568249 10000000000 24109124426021 50000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1245165371/10000000000 : ℝ), (635834617/1250000000 : ℝ), (5495568249/10000000000 : ℝ)] ![(789869380889/10000000000000 : ℝ), (4388305732017/10000000000000 : ℝ), (24109124426021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1245165371/10000000000 : ℝ)|^5711 ≤ (789869380889/10000000000000 : ℝ)^4687
        have hw : |(-1245165371/10000000000 : ℝ)|=(1245165371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635834617/1250000000 : ℝ)|^5711 ≤ (4388305732017/10000000000000 : ℝ)^4687
        have hw : |(635834617/1250000000 : ℝ)|=(635834617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495568249/10000000000 : ℝ)|^5711 ≤ (24109124426021/50000000000000 : ℝ)^4687
        have hw : |(5495568249/10000000000 : ℝ)|=(5495568249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_5 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226941947/10000000000 : ℝ)*x 0 + (-262590367/2500000000 : ℝ)*x 1 + (219822719/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226941947/10000000000 : ℝ)^5711 ≤ (45361914577563/100000000000000 : ℝ)^4687 := by
    have hnat : (5226941947 : ℕ)^5711*100000000000000^4687 ≤ 45361914577563^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226941947 10000000000 45361914577563 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262590367/2500000000 : ℝ)^5711 ≤ (6419839479917/100000000000000 : ℝ)^4687 := by
    have hnat : (262590367 : ℕ)^5711*100000000000000^4687 ≤ 6419839479917^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262590367 2500000000 6419839479917 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219822719/400000000 : ℝ)^5711 ≤ (12054561480681/25000000000000 : ℝ)^4687 := by
    have hnat : (219822719 : ℕ)^5711*25000000000000^4687 ≤ 12054561480681^4687*400000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219822719 400000000 12054561480681 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226941947/10000000000 : ℝ), (-262590367/2500000000 : ℝ), (219822719/400000000 : ℝ)] ![(45361914577563/100000000000000 : ℝ), (6419839479917/100000000000000 : ℝ), (12054561480681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226941947/10000000000 : ℝ)|^5711 ≤ (45361914577563/100000000000000 : ℝ)^4687
        have hw : |(5226941947/10000000000 : ℝ)|=(5226941947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262590367/2500000000 : ℝ)|^5711 ≤ (6419839479917/100000000000000 : ℝ)^4687
        have hw : |(-262590367/2500000000 : ℝ)|=(262590367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219822719/400000000 : ℝ)|^5711 ≤ (12054561480681/25000000000000 : ℝ)^4687
        have hw : |(219822719/400000000 : ℝ)|=(219822719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_6 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226941819/10000000000 : ℝ)*x 0 + (2747784027/5000000000 : ℝ)*x 1 + (-1050361537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226941819/10000000000 : ℝ)^5711 ≤ (5670239153003/12500000000000 : ℝ)^4687 := by
    have hnat : (5226941819 : ℕ)^5711*12500000000000^4687 ≤ 5670239153003^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226941819 10000000000 5670239153003 12500000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747784027/5000000000 : ℝ)^5711 ≤ (12054561691827/25000000000000 : ℝ)^4687 := by
    have hnat : (2747784027 : ℕ)^5711*25000000000000^4687 ≤ 12054561691827^4687*5000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747784027 5000000000 12054561691827 25000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050361537/10000000000 : ℝ)^5711 ≤ (1283967998757/20000000000000 : ℝ)^4687 := by
    have hnat : (1050361537 : ℕ)^5711*20000000000000^4687 ≤ 1283967998757^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050361537 10000000000 1283967998757 20000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226941819/10000000000 : ℝ), (2747784027/5000000000 : ℝ), (-1050361537/10000000000 : ℝ)] ![(5670239153003/12500000000000 : ℝ), (12054561691827/25000000000000 : ℝ), (1283967998757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226941819/10000000000 : ℝ)|^5711 ≤ (5670239153003/12500000000000 : ℝ)^4687
        have hw : |(5226941819/10000000000 : ℝ)|=(5226941819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747784027/5000000000 : ℝ)|^5711 ≤ (12054561691827/25000000000000 : ℝ)^4687
        have hw : |(2747784027/5000000000 : ℝ)|=(2747784027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050361537/10000000000 : ℝ)|^5711 ≤ (1283967998757/20000000000000 : ℝ)^4687
        have hw : |(-1050361537/10000000000 : ℝ)|=(1050361537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1746_s2_7 (p : ℝ) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4030448441/10000000000 : ℝ)*x 0 + (188895001/400000000 : ℝ)*x 1 + (850211317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030448441/10000000000 : ℝ)^5711 ≤ (33047019835049/100000000000000 : ℝ)^4687 := by
    have hnat : (4030448441 : ℕ)^5711*100000000000000^4687 ≤ 33047019835049^4687*10000000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030448441 10000000000 33047019835049 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188895001/400000000 : ℝ)^5711 ≤ (40084101137673/100000000000000 : ℝ)^4687 := by
    have hnat : (188895001 : ℕ)^5711*100000000000000^4687 ≤ 40084101137673^4687*400000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188895001 400000000 40084101137673 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850211317/2500000000 : ℝ)^5711 ≤ (26868879016101/100000000000000 : ℝ)^4687 := by
    have hnat : (850211317 : ℕ)^5711*100000000000000^4687 ≤ 26868879016101^4687*2500000000^5711 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850211317 2500000000 26868879016101 100000000000000 5711 4687 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5711/1024 : ℝ)) 5711 4687 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030448441/10000000000 : ℝ), (188895001/400000000 : ℝ), (850211317/2500000000 : ℝ)] ![(33047019835049/100000000000000 : ℝ), (40084101137673/100000000000000 : ℝ), (26868879016101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030448441/10000000000 : ℝ)|^5711 ≤ (33047019835049/100000000000000 : ℝ)^4687
        have hw : |(4030448441/10000000000 : ℝ)|=(4030448441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188895001/400000000 : ℝ)|^5711 ≤ (40084101137673/100000000000000 : ℝ)^4687
        have hw : |(188895001/400000000 : ℝ)|=(188895001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850211317/2500000000 : ℝ)|^5711 ≤ (26868879016101/100000000000000 : ℝ)^4687
        have hw : |(850211317/2500000000 : ℝ)|=(850211317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1746_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4493/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3611/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4459/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9069/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4459/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4459/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9069/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4459/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4459/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9069/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4459/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4459/50000 : ℝ) ^ (5695/1024 : ℝ) ≤ (145173691490859/100000000000000000000 : ℝ) := by
    have hpowers : (4459/50000 : ℝ)^5695 ≤ (145173691490859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4459 : ℕ)^5695*100000000000000000000^1024 ≤ 145173691490859^1024*50000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4459 50000 145173691490859 100000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4459/50000 : ℝ)) (X := (145173691490859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9069/50000 : ℝ) ^ (5695/1024 : ℝ) ≤ (7527097779960991/100000000000000000000 : ℝ) := by
    have hpowers : (9069/50000 : ℝ)^5695 ≤ (7527097779960991/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9069 : ℕ)^5695*100000000000000000000^1024 ≤ 7527097779960991^1024*50000^5695 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9069 50000 7527097779960991 100000000000000000000 5695 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9069/50000 : ℝ)) (X := (7527097779960991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000145173691490859/50000000000000000000 : ℝ) ≤ (10000005220638563/10000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (50000145173691490859/50000000000000000000 : ℝ)^1024 ≤ (10000005220638563/10000000000000000 : ℝ)^5695 := by
      have hnat : (50000145173691490859 : ℕ)^1024*10000000000000000^5695 ≤ 10000005220638563^5695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000145173691490859 50000000000000000000 10000005220638563 10000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000005220638563/10000000000000000 : ℝ)) (X := (50000145173691490859/50000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000153445429429037/2000000000000000000 : ℝ) ≤ (2500034487088703/2500000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (2000153445429429037/2000000000000000000 : ℝ)^1024 ≤ (2500034487088703/2500000000000000 : ℝ)^5695 := by
      have hnat : (2000153445429429037 : ℕ)^1024*2500000000000000^5695 ≤ 2500034487088703^5695*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000153445429429037 2000000000000000000 2500034487088703 2500000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500034487088703/2500000000000000 : ℝ)) (X := (2000153445429429037/2000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007527097779960991/50000000000000000000 : ℝ) ≤ (10000270676071061/10000000000000000 : ℝ) ^ (5695/1024 : ℝ) := by
    have hpowers : (50007527097779960991/50000000000000000000 : ℝ)^1024 ≤ (10000270676071061/10000000000000000 : ℝ)^5695 := by
      have hnat : (50007527097779960991 : ℕ)^1024*10000000000000000^5695 ≤ 10000270676071061^5695*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007527097779960991 50000000000000000000 10000270676071061 10000000000000000 1024 5695 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000270676071061/10000000000000000 : ℝ)) (X := (50007527097779960991/50000000000000000000 : ℝ)) (by norm_num) 5695 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(145173691490859/100000000000000000000 : ℝ) ≤ ((1440588762542820839/1440625000000000000 : ℝ)+2*(132727716249/922000000000000 : ℝ)*(4459/50000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (1440588762542820839/1440625000000000000 : ℝ)+2*(132727716249/922000000000000 : ℝ)*(4459/50000 : ℝ)=(10000005220638563/10000000000000000 : ℝ) by norm_num, show 1+2*(145173691490859/100000000000000000000 : ℝ)=(50000145173691490859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7527097779960991/100000000000000000000 : ℝ)+(145173691490859/100000000000000000000 : ℝ) ≤ ((1440588762542820839/1440625000000000000 : ℝ)+(132727716249/922000000000000 : ℝ)*((9069/50000 : ℝ)+(4459/50000 : ℝ)))^(5695/1024 : ℝ) := by
    rw [show (1440588762542820839/1440625000000000000 : ℝ)+(132727716249/922000000000000 : ℝ)*((9069/50000 : ℝ)+(4459/50000 : ℝ))=(2500034487088703/2500000000000000 : ℝ) by norm_num, show 1+(7527097779960991/100000000000000000000 : ℝ)+(145173691490859/100000000000000000000 : ℝ)=(2000153445429429037/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7527097779960991/100000000000000000000 : ℝ) ≤ ((1440588762542820839/1440625000000000000 : ℝ)+2*(132727716249/922000000000000 : ℝ)*(9069/50000 : ℝ))^(5695/1024 : ℝ) := by
    rw [show (1440588762542820839/1440625000000000000 : ℝ)+2*(132727716249/922000000000000 : ℝ)*(9069/50000 : ℝ)=(10000270676071061/10000000000000000 : ℝ) by norm_num, show 1+2*(7527097779960991/100000000000000000000 : ℝ)=(50007527097779960991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1440588762542820839/1440625000000000000 : ℝ)*(X 1 0+X 2 0)+(132727716249/922000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (4459/50000 : ℝ)) (hi := (9069/50000 : ℝ)) (c := (1440588762542820839/1440625000000000000 : ℝ)) (alpha := (132727716249/922000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1440588762542820839/1440625000000000000 : ℝ)*(X 0 1+X 2 1)+(132727716249/922000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (4459/50000 : ℝ)) (hi := (9069/50000 : ℝ)) (c := (1440588762542820839/1440625000000000000 : ℝ)) (alpha := (132727716249/922000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1440588762542820839/1440625000000000000 : ℝ)*(X 0 2+X 1 2)+(132727716249/922000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5695/1024 : ℝ)) (lo := (4459/50000 : ℝ)) (hi := (9069/50000 : ℝ)) (c := (1440588762542820839/1440625000000000000 : ℝ)) (alpha := (132727716249/922000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1244805847/10000000000 : ℝ)*X 0 0+(550254401/1000000000 : ℝ)*X 0 1+(158745147/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1334777629/2500000000 : ℝ)*X 1 0+(-916303/6250000 : ℝ)*X 1 1+(5079844697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33369441/62500000 : ℝ)*X 2 0+(2539922357/5000000000 : ℝ)*X 2 1+(-18326059/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2014643189/5000000000 : ℝ)*X 0 0+(675659789/2000000000 : ℝ)*X 0 1+(4744456883/10000000000 : ℝ)*X 0 2+(2014643189/5000000000 : ℝ)*X 1 0+(675659789/2000000000 : ℝ)*X 1 1+(4744456883/10000000000 : ℝ)*X 1 2+(2014643189/5000000000 : ℝ)*X 2 0+(675659789/2000000000 : ℝ)*X 2 1+(4744456883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1245165371/10000000000 : ℝ)*X 0 0+(635834617/1250000000 : ℝ)*X 0 1+(5495568249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226941947/10000000000 : ℝ)*X 1 0+(-262590367/2500000000 : ℝ)*X 1 1+(219822719/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5226941819/10000000000 : ℝ)*X 2 0+(2747784027/5000000000 : ℝ)*X 2 1+(-1050361537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4030448441/10000000000 : ℝ)*X 0 0+(188895001/400000000 : ℝ)*X 0 1+(850211317/2500000000 : ℝ)*X 0 2+(4030448441/10000000000 : ℝ)*X 1 0+(188895001/400000000 : ℝ)*X 1 1+(850211317/2500000000 : ℝ)*X 1 2+(4030448441/10000000000 : ℝ)*X 2 0+(188895001/400000000 : ℝ)*X 2 1+(850211317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1746_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610978030828562539613292597/72031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1201276497/100000000000000 : ℝ)*(base19) + (235913639/20000000000000 : ℝ)*(base23) + (2749959/12500000000000 : ℝ)*(lower2) + (22055403/12500000000000 : ℝ)*(upper3) + (189937173/100000000000000 : ℝ)*(upper5) + (1548876502265741/100000000000000 : ℝ)*(major0) + (1548876502265741/100000000000000 : ℝ)*(major1) + (1548876502265741/100000000000000 : ℝ)*(major2) + (18926056340931/800000000000 : ℝ)*(sp0) + (2365765774562003/100000000000000 : ℝ)*(sp1) + (473153159254061/20000000000000 : ℝ)*(sp2) + (731982709949663/100000000000000 : ℝ)*(sp3) + (79465777/800000000000 : ℝ)*(sp4) + (3036005833/100000000000000 : ℝ)*(sp7) + (91498218244437/12500000000000 : ℝ)*(f.failure) + (4731533951677/200000000000 : ℝ)*(f.sum) + (23296632346809/46100000000000000000000000000 : ℝ)*base65 + (1722846966815380977/288125000000000000000000000000000 : ℝ)*base68 + (109003756204619023/288125000000000000000000000000000 : ℝ)*base69 + (273627602881005977/288125000000000000000000000000000 : ℝ)*base72 + (224689235630491/46100000000000000000000000000 : ℝ)*base74 + (805940340874130977/288125000000000000000000000000000 : ℝ)*base76 + (150320313886494023/288125000000000000000000000000000 : ℝ)*base77 + (968779188202880977/288125000000000000000000000000000 : ℝ)*base80 + (3117735460209/46100000000000000000000000000 : ℝ)*base81 + (6505427/1250000000000000000000 : ℝ)*base89 + (6505427/1250000000000000000000 : ℝ)*base91 + (6505427/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1394675583434363720569713291/144062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (307199037/25000000000000 : ℝ)*(base19) + (609462041/50000000000000 : ℝ)*(base23) + (153747959/100000000000000 : ℝ)*(upper3) + (16551791/50000000000000 : ℝ)*(lower4) + (104724427/50000000000000 : ℝ)*(upper5) + (1601168408773587/100000000000000 : ℝ)*(major0) + (1601168408773587/100000000000000 : ℝ)*(major1) + (1601168408773587/100000000000000 : ℝ)*(major2) + (320159537/4000000000000 : ℝ)*(sp1) + (3691763397/50000000000000 : ℝ)*(sp2) + (305704755315933/12500000000000 : ℝ)*(sp4) + (244562880974289/10000000000000 : ℝ)*(sp5) + (611407360019147/25000000000000 : ℝ)*(sp6) + (756698452318197/100000000000000 : ℝ)*(sp7) + (756698452318197/100000000000000 : ℝ)*(f.failure) + (305704755315933/12500000000000 : ℝ)*(f.sum) + (52367629023863/46100000000000000000000000000 : ℝ)*base65 + (940704862582981639/288125000000000000000000000000000 : ℝ)*base68 + (1719227862259856639/288125000000000000000000000000000 : ℝ)*base70 + (6256910755768361/288125000000000000000000000000000 : ℝ)*base71 + (213298318544663/46100000000000000000000000000 : ℝ)*base73 + (850441506871731639/288125000000000000000000000000000 : ℝ)*base76 + (1256478009120481639/288125000000000000000000000000000 : ℝ)*base78 + (1294815202460481639/288125000000000000000000000000000 : ℝ)*base80 + (20603501519163/46100000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (45234387/10000000000000000000000 : ℝ)*base89 + (45234387/10000000000000000000000 : ℝ)*base91 + (45234387/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1746_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9069/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1746_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1746_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1746_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1746_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1746_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5695/1024 : ℝ) ≤ p) (hpb : p ≤ (5711/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (211599271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3611/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1746_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
