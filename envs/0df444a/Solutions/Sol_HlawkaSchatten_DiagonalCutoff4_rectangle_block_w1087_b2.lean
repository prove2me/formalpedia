-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1087_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:55:10.156996+00:00
-- url     : https://prove2.me/submissions/c92a7fe4-eef4-47a1-b31a-8e236c731f7a

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
theorem support_rectangle_w1087_s6_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096711929/5000000000 : ℝ)*x 0 + (269724553/500000000 : ℝ)*x 1 + (5264360217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096711929/5000000000 : ℝ)^1035 ≤ (832679803583/6250000000000 : ℝ)^779 := by
    have hnat : (1096711929 : ℕ)^1035*6250000000000^779 ≤ 832679803583^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096711929 5000000000 832679803583 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269724553/500000000 : ℝ)^1035 ≤ (44041521725451/100000000000000 : ℝ)^779 := by
    have hnat : (269724553 : ℕ)^1035*100000000000000^779 ≤ 44041521725451^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269724553 500000000 44041521725451 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264360217/10000000000 : ℝ)^1035 ≤ (21317800701149/50000000000000 : ℝ)^779 := by
    have hnat : (5264360217 : ℕ)^1035*50000000000000^779 ≤ 21317800701149^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264360217 10000000000 21317800701149 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096711929/5000000000 : ℝ), (269724553/500000000 : ℝ), (5264360217/10000000000 : ℝ)] ![(832679803583/6250000000000 : ℝ), (44041521725451/100000000000000 : ℝ), (21317800701149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096711929/5000000000 : ℝ)|^1035 ≤ (832679803583/6250000000000 : ℝ)^779
        have hw : |(-1096711929/5000000000 : ℝ)|=(1096711929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269724553/500000000 : ℝ)|^1035 ≤ (44041521725451/100000000000000 : ℝ)^779
        have hw : |(269724553/500000000 : ℝ)|=(269724553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264360217/10000000000 : ℝ)|^1035 ≤ (21317800701149/50000000000000 : ℝ)^779
        have hw : |(5264360217/10000000000 : ℝ)|=(5264360217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672526477/5000000000 : ℝ)*x 0 + (-2259449777/10000000000 : ℝ)*x 1 + (1052872029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672526477/5000000000 : ℝ)^1035 ≤ (21753034749869/50000000000000 : ℝ)^779 := by
    have hnat : (2672526477 : ℕ)^1035*50000000000000^779 ≤ 21753034749869^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672526477 5000000000 21753034749869 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259449777/10000000000 : ℝ)^1035 ≤ (173229123167/1250000000000 : ℝ)^779 := by
    have hnat : (2259449777 : ℕ)^1035*1250000000000^779 ≤ 173229123167^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259449777 10000000000 173229123167 1250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052872029/2000000000 : ℝ)^1035 ≤ (42635600627547/100000000000000 : ℝ)^779 := by
    have hnat : (1052872029 : ℕ)^1035*100000000000000^779 ≤ 42635600627547^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052872029 2000000000 42635600627547 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672526477/5000000000 : ℝ), (-2259449777/10000000000 : ℝ), (1052872029/2000000000 : ℝ)] ![(21753034749869/50000000000000 : ℝ), (173229123167/1250000000000 : ℝ), (42635600627547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672526477/5000000000 : ℝ)|^1035 ≤ (21753034749869/50000000000000 : ℝ)^779
        have hw : |(2672526477/5000000000 : ℝ)|=(2672526477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2259449777/10000000000 : ℝ)|^1035 ≤ (173229123167/1250000000000 : ℝ)^779
        have hw : |(-2259449777/10000000000 : ℝ)|=(2259449777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052872029/2000000000 : ℝ)|^1035 ≤ (42635600627547/100000000000000 : ℝ)^779
        have hw : |(1052872029/2000000000 : ℝ)|=(1052872029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336263223/2500000000 : ℝ)*x 0 + (65804503/125000000 : ℝ)*x 1 + (-451889947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336263223/2500000000 : ℝ)^1035 ≤ (679782325457/1562500000000 : ℝ)^779 := by
    have hnat : (1336263223 : ℕ)^1035*1562500000000^779 ≤ 679782325457^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336263223 2500000000 679782325457 1562500000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65804503/125000000 : ℝ)^1035 ≤ (10658900412447/25000000000000 : ℝ)^779 := by
    have hnat : (65804503 : ℕ)^1035*25000000000000^779 ≤ 10658900412447^779*125000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65804503 125000000 10658900412447 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451889947/2000000000 : ℝ)^1035 ≤ (13858329511097/100000000000000 : ℝ)^779 := by
    have hnat : (451889947 : ℕ)^1035*100000000000000^779 ≤ 13858329511097^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451889947 2000000000 13858329511097 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336263223/2500000000 : ℝ), (65804503/125000000 : ℝ), (-451889947/2000000000 : ℝ)] ![(679782325457/1562500000000 : ℝ), (10658900412447/25000000000000 : ℝ), (13858329511097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336263223/2500000000 : ℝ)|^1035 ≤ (679782325457/1562500000000 : ℝ)^779
        have hw : |(1336263223/2500000000 : ℝ)|=(1336263223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65804503/125000000 : ℝ)|^1035 ≤ (10658900412447/25000000000000 : ℝ)^779
        have hw : |(65804503/125000000 : ℝ)|=(65804503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451889947/2000000000 : ℝ)|^1035 ≤ (13858329511097/100000000000000 : ℝ)^779
        have hw : |(-451889947/2000000000 : ℝ)|=(451889947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4372455677/10000000000 : ℝ)*x 0 + (2123147543/5000000000 : ℝ)*x 1 + (562799609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372455677/10000000000 : ℝ)^1035 ≤ (8329104201517/25000000000000 : ℝ)^779 := by
    have hnat : (4372455677 : ℕ)^1035*25000000000000^779 ≤ 8329104201517^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372455677 10000000000 8329104201517 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123147543/5000000000 : ℝ)^1035 ≤ (6409061987837/20000000000000 : ℝ)^779 := by
    have hnat : (2123147543 : ℕ)^1035*20000000000000^779 ≤ 6409061987837^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123147543 5000000000 6409061987837 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562799609/1250000000 : ℝ)^1035 ≤ (17319136620567/50000000000000 : ℝ)^779 := by
    have hnat : (562799609 : ℕ)^1035*50000000000000^779 ≤ 17319136620567^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562799609 1250000000 17319136620567 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372455677/10000000000 : ℝ), (2123147543/5000000000 : ℝ), (562799609/1250000000 : ℝ)] ![(8329104201517/25000000000000 : ℝ), (6409061987837/20000000000000 : ℝ), (17319136620567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372455677/10000000000 : ℝ)|^1035 ≤ (8329104201517/25000000000000 : ℝ)^779
        have hw : |(4372455677/10000000000 : ℝ)|=(4372455677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123147543/5000000000 : ℝ)|^1035 ≤ (6409061987837/20000000000000 : ℝ)^779
        have hw : |(2123147543/5000000000 : ℝ)|=(2123147543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562799609/1250000000 : ℝ)|^1035 ≤ (17319136620567/50000000000000 : ℝ)^779
        have hw : |(562799609/1250000000 : ℝ)|=(562799609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-548357237/2500000000 : ℝ)*x 0 + (5264688801/10000000000 : ℝ)*x 1 + (5394161309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548357237/2500000000 : ℝ)^1035 ≤ (6661458967049/50000000000000 : ℝ)^779 := by
    have hnat : (548357237 : ℕ)^1035*50000000000000^779 ≤ 6661458967049^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548357237 2500000000 6661458967049 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264688801/10000000000 : ℝ)^1035 ≤ (21319568572091/50000000000000 : ℝ)^779 := by
    have hnat : (5264688801 : ℕ)^1035*50000000000000^779 ≤ 21319568572091^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264688801 10000000000 21319568572091 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394161309/10000000000 : ℝ)^1035 ≤ (8807588982071/20000000000000 : ℝ)^779 := by
    have hnat : (5394161309 : ℕ)^1035*20000000000000^779 ≤ 8807588982071^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394161309 10000000000 8807588982071 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548357237/2500000000 : ℝ), (5264688801/10000000000 : ℝ), (5394161309/10000000000 : ℝ)] ![(6661458967049/50000000000000 : ℝ), (21319568572091/50000000000000 : ℝ), (8807588982071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548357237/2500000000 : ℝ)|^1035 ≤ (6661458967049/50000000000000 : ℝ)^779
        have hw : |(-548357237/2500000000 : ℝ)|=(548357237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264688801/10000000000 : ℝ)|^1035 ≤ (21319568572091/50000000000000 : ℝ)^779
        have hw : |(5264688801/10000000000 : ℝ)|=(5264688801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394161309/10000000000 : ℝ)|^1035 ≤ (8807588982071/20000000000000 : ℝ)^779
        have hw : |(5394161309/10000000000 : ℝ)|=(5394161309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656110733/5000000000 : ℝ)*x 0 + (-532412101/2500000000 : ℝ)*x 1 + (2697080649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656110733/5000000000 : ℝ)^1035 ≤ (5393922110663/12500000000000 : ℝ)^779 := by
    have hnat : (2656110733 : ℕ)^1035*12500000000000^779 ≤ 5393922110663^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656110733 5000000000 5393922110663 12500000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532412101/2500000000 : ℝ)^1035 ≤ (6405339155857/50000000000000 : ℝ)^779 := by
    have hnat : (532412101 : ℕ)^1035*50000000000000^779 ≤ 6405339155857^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532412101 2500000000 6405339155857 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697080649/5000000000 : ℝ)^1035 ≤ (44037944791039/100000000000000 : ℝ)^779 := by
    have hnat : (2697080649 : ℕ)^1035*100000000000000^779 ≤ 44037944791039^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697080649 5000000000 44037944791039 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656110733/5000000000 : ℝ), (-532412101/2500000000 : ℝ), (2697080649/5000000000 : ℝ)] ![(5393922110663/12500000000000 : ℝ), (6405339155857/50000000000000 : ℝ), (44037944791039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656110733/5000000000 : ℝ)|^1035 ≤ (5393922110663/12500000000000 : ℝ)^779
        have hw : |(2656110733/5000000000 : ℝ)|=(2656110733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532412101/2500000000 : ℝ)|^1035 ≤ (6405339155857/50000000000000 : ℝ)^779
        have hw : |(-532412101/2500000000 : ℝ)|=(532412101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697080649/5000000000 : ℝ)|^1035 ≤ (44037944791039/100000000000000 : ℝ)^779
        have hw : |(2697080649/5000000000 : ℝ)|=(2697080649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312221431/10000000000 : ℝ)*x 0 + (2697080647/5000000000 : ℝ)*x 1 + (-266206057/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312221431/10000000000 : ℝ)^1035 ≤ (43151376507567/100000000000000 : ℝ)^779 := by
    have hnat : (5312221431 : ℕ)^1035*100000000000000^779 ≤ 43151376507567^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312221431 10000000000 43151376507567 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697080647/5000000000 : ℝ)^1035 ≤ (44037944747651/100000000000000 : ℝ)^779 := by
    have hnat : (2697080647 : ℕ)^1035*100000000000000^779 ≤ 44037944747651^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697080647 5000000000 44037944747651 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266206057/1250000000 : ℝ)^1035 ≤ (12810678727309/100000000000000 : ℝ)^779 := by
    have hnat : (266206057 : ℕ)^1035*100000000000000^779 ≤ 12810678727309^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266206057 1250000000 12810678727309 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312221431/10000000000 : ℝ), (2697080647/5000000000 : ℝ), (-266206057/1250000000 : ℝ)] ![(43151376507567/100000000000000 : ℝ), (44037944747651/100000000000000 : ℝ), (12810678727309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312221431/10000000000 : ℝ)|^1035 ≤ (43151376507567/100000000000000 : ℝ)^779
        have hw : |(5312221431/10000000000 : ℝ)|=(5312221431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697080647/5000000000 : ℝ)|^1035 ≤ (44037944747651/100000000000000 : ℝ)^779
        have hw : |(2697080647/5000000000 : ℝ)|=(2697080647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266206057/1250000000 : ℝ)|^1035 ≤ (12810678727309/100000000000000 : ℝ)^779
        have hw : |(-266206057/1250000000 : ℝ)|=(266206057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s6_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4372465937/10000000000 : ℝ)*x 0 + (4501750197/10000000000 : ℝ)*x 1 + (66358499/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372465937/10000000000 : ℝ)^1035 ≤ (260285317769/781250000000 : ℝ)^779 := by
    have hnat : (4372465937 : ℕ)^1035*781250000000^779 ≤ 260285317769^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372465937 10000000000 260285317769 781250000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501750197/10000000000 : ℝ)^1035 ≤ (17315831698841/50000000000000 : ℝ)^779 := by
    have hnat : (4501750197 : ℕ)^1035*50000000000000^779 ≤ 17315831698841^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501750197 10000000000 17315831698841 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66358499/156250000 : ℝ)^1035 ≤ (32051815914483/100000000000000 : ℝ)^779 := by
    have hnat : (66358499 : ℕ)^1035*100000000000000^779 ≤ 32051815914483^779*156250000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66358499 156250000 32051815914483 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372465937/10000000000 : ℝ), (4501750197/10000000000 : ℝ), (66358499/156250000 : ℝ)] ![(260285317769/781250000000 : ℝ), (17315831698841/50000000000000 : ℝ), (32051815914483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372465937/10000000000 : ℝ)|^1035 ≤ (260285317769/781250000000 : ℝ)^779
        have hw : |(4372465937/10000000000 : ℝ)|=(4372465937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501750197/10000000000 : ℝ)|^1035 ≤ (17315831698841/50000000000000 : ℝ)^779
        have hw : |(4501750197/10000000000 : ℝ)|=(4501750197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66358499/156250000 : ℝ)|^1035 ≤ (32051815914483/100000000000000 : ℝ)^779
        have hw : |(66358499/156250000 : ℝ)|=(66358499/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1127/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14067/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14067/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/3125 : ℝ) ^ (8279/2048 : ℝ) ≤ (14504118904198111/100000000000000000000 : ℝ) := by
    have hpowers : (351/3125 : ℝ)^8279 ≤ (14504118904198111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (351 : ℕ)^8279*100000000000000000000^2048 ≤ 14504118904198111^2048*3125^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 3125 14504118904198111 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/3125 : ℝ)) (X := (14504118904198111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14067/100000 : ℝ) ^ (8279/2048 : ℝ) ≤ (18013211741013399/50000000000000000000 : ℝ) := by
    have hpowers : (14067/100000 : ℝ)^8279 ≤ (18013211741013399/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14067 : ℕ)^8279*50000000000000000000^2048 ≤ 18013211741013399^2048*100000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14067 100000 18013211741013399 50000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14067/100000 : ℝ)) (X := (18013211741013399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014504118904198111/50000000000000000000 : ℝ) ≤ (5000358753393787/5000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50014504118904198111/50000000000000000000 : ℝ)^2048 ≤ (5000358753393787/5000000000000000 : ℝ)^8279 := by
      have hnat : (50014504118904198111 : ℕ)^2048*5000000000000000^8279 ≤ 5000358753393787^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014504118904198111 50000000000000000000 5000358753393787 5000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000358753393787/5000000000000000 : ℝ)) (X := (50014504118904198111/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050530542386224909/100000000000000000000 : ℝ) ≤ (156269527358057/156250000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (100050530542386224909/100000000000000000000 : ℝ)^2048 ≤ (156269527358057/156250000000000 : ℝ)^8279 := by
      have hnat : (100050530542386224909 : ℕ)^2048*156250000000000^8279 ≤ 156269527358057^8279*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050530542386224909 100000000000000000000 156269527358057 156250000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156269527358057/156250000000000 : ℝ)) (X := (100050530542386224909/100000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018013211741013399/25000000000000000000 : ℝ) ≤ (5000890997521861/5000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (25018013211741013399/25000000000000000000 : ℝ)^2048 ≤ (5000890997521861/5000000000000000 : ℝ)^8279 := by
      have hnat : (25018013211741013399 : ℕ)^2048*5000000000000000^8279 ≤ 5000890997521861^8279*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018013211741013399 25000000000000000000 5000890997521861 5000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000890997521861/5000000000000000 : ℝ)) (X := (25018013211741013399/25000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14504118904198111/100000000000000000000 : ℝ) ≤ ((174938751849689617/175000000000000000 : ℝ)+2*(88707354679/47250000000000 : ℝ)*(351/3125 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (174938751849689617/175000000000000000 : ℝ)+2*(88707354679/47250000000000 : ℝ)*(351/3125 : ℝ)=(5000358753393787/5000000000000000 : ℝ) by norm_num, show 1+2*(14504118904198111/100000000000000000000 : ℝ)=(50014504118904198111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18013211741013399/50000000000000000000 : ℝ)+(14504118904198111/100000000000000000000 : ℝ) ≤ ((174938751849689617/175000000000000000 : ℝ)+(88707354679/47250000000000 : ℝ)*((14067/100000 : ℝ)+(351/3125 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (174938751849689617/175000000000000000 : ℝ)+(88707354679/47250000000000 : ℝ)*((14067/100000 : ℝ)+(351/3125 : ℝ))=(156269527358057/156250000000000 : ℝ) by norm_num, show 1+(18013211741013399/50000000000000000000 : ℝ)+(14504118904198111/100000000000000000000 : ℝ)=(100050530542386224909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18013211741013399/50000000000000000000 : ℝ) ≤ ((174938751849689617/175000000000000000 : ℝ)+2*(88707354679/47250000000000 : ℝ)*(14067/100000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (174938751849689617/175000000000000000 : ℝ)+2*(88707354679/47250000000000 : ℝ)*(14067/100000 : ℝ)=(5000890997521861/5000000000000000 : ℝ) by norm_num, show 1+2*(18013211741013399/50000000000000000000 : ℝ)=(25018013211741013399/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (174938751849689617/175000000000000000 : ℝ)*(X 1 0+X 2 0)+(88707354679/47250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (174938751849689617/175000000000000000 : ℝ)) (alpha := (88707354679/47250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (174938751849689617/175000000000000000 : ℝ)*(X 0 1+X 2 1)+(88707354679/47250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (174938751849689617/175000000000000000 : ℝ)) (alpha := (88707354679/47250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (174938751849689617/175000000000000000 : ℝ)*(X 0 2+X 1 2)+(88707354679/47250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (14067/100000 : ℝ)) (c := (174938751849689617/175000000000000000 : ℝ)) (alpha := (88707354679/47250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1096711929/5000000000 : ℝ)*X 0 0+(269724553/500000000 : ℝ)*X 0 1+(5264360217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672526477/5000000000 : ℝ)*X 1 0+(-2259449777/10000000000 : ℝ)*X 1 1+(1052872029/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336263223/2500000000 : ℝ)*X 2 0+(65804503/125000000 : ℝ)*X 2 1+(-451889947/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372455677/10000000000 : ℝ)*X 0 0+(2123147543/5000000000 : ℝ)*X 0 1+(562799609/1250000000 : ℝ)*X 0 2+(4372455677/10000000000 : ℝ)*X 1 0+(2123147543/5000000000 : ℝ)*X 1 1+(562799609/1250000000 : ℝ)*X 1 2+(4372455677/10000000000 : ℝ)*X 2 0+(2123147543/5000000000 : ℝ)*X 2 1+(562799609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548357237/2500000000 : ℝ)*X 0 0+(5264688801/10000000000 : ℝ)*X 0 1+(5394161309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656110733/5000000000 : ℝ)*X 1 0+(-532412101/2500000000 : ℝ)*X 1 1+(2697080649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312221431/10000000000 : ℝ)*X 2 0+(2697080647/5000000000 : ℝ)*X 2 1+(-266206057/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372465937/10000000000 : ℝ)*X 0 0+(4501750197/10000000000 : ℝ)*X 0 1+(66358499/156250000 : ℝ)*X 0 2+(4372465937/10000000000 : ℝ)*X 1 0+(4501750197/10000000000 : ℝ)*X 1 1+(66358499/156250000 : ℝ)*X 1 2+(4372465937/10000000000 : ℝ)*X 2 0+(4501750197/10000000000 : ℝ)*X 2 1+(66358499/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (668574996276984116284389137/78750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1592304071/100000000000000 : ℝ)*(base19) + (32767967/2500000000000 : ℝ)*(base23) + (128345589/50000000000000 : ℝ)*(upper3) + (102864099/100000000000000 : ℝ)*(upper4) + (166828131/100000000000000 : ℝ)*(upper5) + (5794686876781757/100000000000000 : ℝ)*(major0) + (5794686876781757/100000000000000 : ℝ)*(major1) + (5794686876781757/100000000000000 : ℝ)*(major2) + (7684609438571637/100000000000000 : ℝ)*(sp0) + (3842320950619609/50000000000000 : ℝ)*(sp1) + (240145068213269/3125000000000 : ℝ)*(sp2) + (1952356272539873/50000000000000 : ℝ)*(sp3) + (34054971651/100000000000000 : ℝ)*(sp4) + (8715972881/50000000000000 : ℝ)*(sp7) + (976182494256377/25000000000000 : ℝ)*(f.failure) + (960580436692911/12500000000000 : ℝ)*(f.sum) + (1810169489507/590625000000000000000000000 : ℝ)*base65 + (2903638160521560863/472500000000000000000000000000000 : ℝ)*base67 + (1613816547774060863/472500000000000000000000000000000 : ℝ)*base69 + (2495829048864060863/472500000000000000000000000000000 : ℝ)*base71 + (555439552553/2362500000000000000000000000 : ℝ)*base73 + (893622932120939137/472500000000000000000000000000000 : ℝ)*base76 + (4727569683125939137/472500000000000000000000000000000 : ℝ)*base78 + (10987857892869060863/472500000000000000000000000000000 : ℝ)*base79 + (4003443575197/2362500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20411413/2500000000000000000000 : ℝ)*base90 + (20411413/2500000000000000000000 : ℝ)*base92 + (20411413/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (375227882741275000135494167/39375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2448951433/100000000000000 : ℝ)*(base19) + (2368989773/100000000000000 : ℝ)*(base23) + (424641/50000000000000 : ℝ)*(upper2) + (58610981/25000000000000 : ℝ)*(upper3) + (8475813/3125000000000 : ℝ)*(upper5) + (5824098927449587/100000000000000 : ℝ)*(major0) + (5824098927449587/100000000000000 : ℝ)*(major1) + (5824098927449587/100000000000000 : ℝ)*(major2) + (213068117/312500000000 : ℝ)*(sp1) + (63218953031/100000000000000 : ℝ)*(sp2) + (7723648350249189/100000000000000 : ℝ)*(sp4) + (7723577719500317/100000000000000 : ℝ)*(sp5) + (3861791381153193/50000000000000 : ℝ)*(sp6) + (1962274593498369/50000000000000 : ℝ)*(sp7) + (1962274593498369/50000000000000 : ℝ)*(f.failure) + (7723648350249189/100000000000000 : ℝ)*(f.sum) + (332455701749/1181250000000000000000000000 : ℝ)*base65 + (3454496546920430833/472500000000000000000000000000000 : ℝ)*base67 + (7012979383255430833/472500000000000000000000000000000 : ℝ)*base69 + (2952918238722069167/472500000000000000000000000000000 : ℝ)*base72 + (2674694778899/1181250000000000000000000000 : ℝ)*base73 + (6234898577042930833/472500000000000000000000000000000 : ℝ)*base75 + (4704779860517930833/472500000000000000000000000000000 : ℝ)*base77 + (3706585439132930833/472500000000000000000000000000000 : ℝ)*base79 + (12586409391071/4725000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (44723261/5000000000000000000000 : ℝ)*base90 + (44723261/5000000000000000000000 : ℝ)*base92 + (44723261/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1087_s7_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-68545641/312500000 : ℝ)*x 0 + (2697037317/5000000000 : ℝ)*x 1 + (2632376249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68545641/312500000 : ℝ)^1035 ≤ (2664634531839/20000000000000 : ℝ)^779 := by
    have hnat : (68545641 : ℕ)^1035*20000000000000^779 ≤ 2664634531839^779*312500000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68545641 312500000 2664634531839 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697037317/5000000000 : ℝ)^1035 ≤ (22018502378489/50000000000000 : ℝ)^779 := by
    have hnat : (2697037317 : ℕ)^1035*50000000000000^779 ≤ 22018502378489^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697037317 5000000000 22018502378489 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632376249/5000000000 : ℝ)^1035 ≤ (42639822566809/100000000000000 : ℝ)^779 := by
    have hnat : (2632376249 : ℕ)^1035*100000000000000^779 ≤ 42639822566809^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632376249 5000000000 42639822566809 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68545641/312500000 : ℝ), (2697037317/5000000000 : ℝ), (2632376249/5000000000 : ℝ)] ![(2664634531839/20000000000000 : ℝ), (22018502378489/50000000000000 : ℝ), (42639822566809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68545641/312500000 : ℝ)|^1035 ≤ (2664634531839/20000000000000 : ℝ)^779
        have hw : |(-68545641/312500000 : ℝ)|=(68545641/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697037317/5000000000 : ℝ)|^1035 ≤ (22018502378489/50000000000000 : ℝ)^779
        have hw : |(2697037317/5000000000 : ℝ)|=(2697037317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632376249/5000000000 : ℝ)|^1035 ≤ (42639822566809/100000000000000 : ℝ)^779
        have hw : |(2632376249/5000000000 : ℝ)|=(2632376249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672474199/5000000000 : ℝ)*x 0 + (-2259070127/10000000000 : ℝ)*x 1 + (5264752731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672474199/5000000000 : ℝ)^1035 ≤ (2719058674837/6250000000000 : ℝ)^779 := by
    have hnat : (2672474199 : ℕ)^1035*6250000000000^779 ≤ 2719058674837^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672474199 5000000000 2719058674837 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259070127/10000000000 : ℝ)^1035 ≤ (692761806133/5000000000000 : ℝ)^779 := by
    have hnat : (2259070127 : ℕ)^1035*5000000000000^779 ≤ 692761806133^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259070127 10000000000 692761806133 5000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264752731/10000000000 : ℝ)^1035 ≤ (42639825074051/100000000000000 : ℝ)^779 := by
    have hnat : (5264752731 : ℕ)^1035*100000000000000^779 ≤ 42639825074051^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264752731 10000000000 42639825074051 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672474199/5000000000 : ℝ), (-2259070127/10000000000 : ℝ), (5264752731/10000000000 : ℝ)] ![(2719058674837/6250000000000 : ℝ), (692761806133/5000000000000 : ℝ), (42639825074051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672474199/5000000000 : ℝ)|^1035 ≤ (2719058674837/6250000000000 : ℝ)^779
        have hw : |(2672474199/5000000000 : ℝ)|=(2672474199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2259070127/10000000000 : ℝ)|^1035 ≤ (692761806133/5000000000000 : ℝ)^779
        have hw : |(-2259070127/10000000000 : ℝ)|=(2259070127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264752731/10000000000 : ℝ)|^1035 ≤ (42639825074051/100000000000000 : ℝ)^779
        have hw : |(5264752731/10000000000 : ℝ)|=(5264752731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344948911/10000000000 : ℝ)*x 0 + (1052950473/2000000000 : ℝ)*x 1 + (-282383741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344948911/10000000000 : ℝ)^1035 ≤ (43504944345121/100000000000000 : ℝ)^779 := by
    have hnat : (5344948911 : ℕ)^1035*100000000000000^779 ≤ 43504944345121^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344948911 10000000000 43504944345121 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052950473/2000000000 : ℝ)^1035 ≤ (10659955283909/25000000000000 : ℝ)^779 := by
    have hnat : (1052950473 : ℕ)^1035*25000000000000^779 ≤ 10659955283909^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052950473 2000000000 10659955283909 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282383741/1250000000 : ℝ)^1035 ≤ (13855234501073/100000000000000 : ℝ)^779 := by
    have hnat : (282383741 : ℕ)^1035*100000000000000^779 ≤ 13855234501073^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282383741 1250000000 13855234501073 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344948911/10000000000 : ℝ), (1052950473/2000000000 : ℝ), (-282383741/1250000000 : ℝ)] ![(43504944345121/100000000000000 : ℝ), (10659955283909/25000000000000 : ℝ), (13855234501073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344948911/10000000000 : ℝ)|^1035 ≤ (43504944345121/100000000000000 : ℝ)^779
        have hw : |(5344948911/10000000000 : ℝ)|=(5344948911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052950473/2000000000 : ℝ)|^1035 ≤ (10659955283909/25000000000000 : ℝ)^779
        have hw : |(1052950473/2000000000 : ℝ)|=(1052950473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282383741/1250000000 : ℝ)|^1035 ≤ (13855234501073/100000000000000 : ℝ)^779
        have hw : |(-282383741/1250000000 : ℝ)|=(282383741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (27327979/62500000 : ℝ)*x 0 + (1061772073/2500000000 : ℝ)*x 1 + (4501597977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27327979/62500000 : ℝ)^1035 ≤ (16658314513823/50000000000000 : ℝ)^779 := by
    have hnat : (27327979 : ℕ)^1035*50000000000000^779 ≤ 16658314513823^779*62500000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27327979 62500000 16658314513823 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061772073/2500000000 : ℝ)^1035 ≤ (16026631703403/50000000000000 : ℝ)^779 := by
    have hnat : (1061772073 : ℕ)^1035*50000000000000^779 ≤ 16026631703403^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061772073 2500000000 16026631703403 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501597977/10000000000 : ℝ)^1035 ≤ (2164381722529/6250000000000 : ℝ)^779 := by
    have hnat : (4501597977 : ℕ)^1035*6250000000000^779 ≤ 2164381722529^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501597977 10000000000 2164381722529 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27327979/62500000 : ℝ), (1061772073/2500000000 : ℝ), (4501597977/10000000000 : ℝ)] ![(16658314513823/50000000000000 : ℝ), (16026631703403/50000000000000 : ℝ), (2164381722529/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27327979/62500000 : ℝ)|^1035 ≤ (16658314513823/50000000000000 : ℝ)^779
        have hw : |(27327979/62500000 : ℝ)|=(27327979/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061772073/2500000000 : ℝ)|^1035 ≤ (16026631703403/50000000000000 : ℝ)^779
        have hw : |(1061772073/2500000000 : ℝ)|=(1061772073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501597977/10000000000 : ℝ)|^1035 ≤ (2164381722529/6250000000000 : ℝ)^779
        have hw : |(4501597977/10000000000 : ℝ)|=(4501597977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-548366441/2500000000 : ℝ)*x 0 + (1053015421/2000000000 : ℝ)*x 1 + (5393748691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548366441/2500000000 : ℝ)^1035 ≤ (6661607521777/50000000000000 : ℝ)^779 := by
    have hnat : (548366441 : ℕ)^1035*50000000000000^779 ≤ 6661607521777^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548366441 2500000000 6661607521777 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053015421/2000000000 : ℝ)^1035 ≤ (8528663119823/20000000000000 : ℝ)^779 := by
    have hnat : (1053015421 : ℕ)^1035*20000000000000^779 ≤ 8528663119823^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053015421 2000000000 8528663119823 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393748691/10000000000 : ℝ)^1035 ≤ (11008367334153/25000000000000 : ℝ)^779 := by
    have hnat : (5393748691 : ℕ)^1035*25000000000000^779 ≤ 11008367334153^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393748691 10000000000 11008367334153 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548366441/2500000000 : ℝ), (1053015421/2000000000 : ℝ), (5393748691/10000000000 : ℝ)] ![(6661607521777/50000000000000 : ℝ), (8528663119823/20000000000000 : ℝ), (11008367334153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548366441/2500000000 : ℝ)|^1035 ≤ (6661607521777/50000000000000 : ℝ)^779
        have hw : |(-548366441/2500000000 : ℝ)|=(548366441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053015421/2000000000 : ℝ)|^1035 ≤ (8528663119823/20000000000000 : ℝ)^779
        have hw : |(1053015421/2000000000 : ℝ)|=(1053015421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393748691/10000000000 : ℝ)|^1035 ≤ (11008367334153/25000000000000 : ℝ)^779
        have hw : |(5393748691/10000000000 : ℝ)|=(5393748691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (106246419/200000000 : ℝ)*x 0 + (-2130074017/10000000000 : ℝ)*x 1 + (5393748697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106246419/200000000 : ℝ)^1035 ≤ (43152450567997/100000000000000 : ℝ)^779 := by
    have hnat : (106246419 : ℕ)^1035*100000000000000^779 ≤ 43152450567997^779*200000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106246419 200000000 43152450567997 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130074017/10000000000 : ℝ)^1035 ≤ (102512640109/800000000000 : ℝ)^779 := by
    have hnat : (2130074017 : ℕ)^1035*800000000000^779 ≤ 102512640109^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130074017 10000000000 102512640109 800000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393748697/10000000000 : ℝ)^1035 ≤ (11008367350423/25000000000000 : ℝ)^779 := by
    have hnat : (5393748697 : ℕ)^1035*25000000000000^779 ≤ 11008367350423^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393748697 10000000000 11008367350423 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106246419/200000000 : ℝ), (-2130074017/10000000000 : ℝ), (5393748697/10000000000 : ℝ)] ![(43152450567997/100000000000000 : ℝ), (102512640109/800000000000 : ℝ), (11008367350423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106246419/200000000 : ℝ)|^1035 ≤ (43152450567997/100000000000000 : ℝ)^779
        have hw : |(106246419/200000000 : ℝ)|=(106246419/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130074017/10000000000 : ℝ)|^1035 ≤ (102512640109/800000000000 : ℝ)^779
        have hw : |(-2130074017/10000000000 : ℝ)|=(2130074017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393748697/10000000000 : ℝ)|^1035 ≤ (11008367350423/25000000000000 : ℝ)^779
        have hw : |(5393748697/10000000000 : ℝ)|=(5393748697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656160471/5000000000 : ℝ)*x 0 + (5393748701/10000000000 : ℝ)*x 1 + (-266259253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656160471/5000000000 : ℝ)^1035 ≤ (43152450481657/100000000000000 : ℝ)^779 := by
    have hnat : (2656160471 : ℕ)^1035*100000000000000^779 ≤ 43152450481657^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656160471 5000000000 43152450481657 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393748701/10000000000 : ℝ)^1035 ≤ (22016734722539/50000000000000 : ℝ)^779 := by
    have hnat : (5393748701 : ℕ)^1035*50000000000000^779 ≤ 22016734722539^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393748701 10000000000 22016734722539 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266259253/1250000000 : ℝ)^1035 ≤ (6407040034787/50000000000000 : ℝ)^779 := by
    have hnat : (266259253 : ℕ)^1035*50000000000000^779 ≤ 6407040034787^779*1250000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266259253 1250000000 6407040034787 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656160471/5000000000 : ℝ), (5393748701/10000000000 : ℝ), (-266259253/1250000000 : ℝ)] ![(43152450481657/100000000000000 : ℝ), (22016734722539/50000000000000 : ℝ), (6407040034787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656160471/5000000000 : ℝ)|^1035 ≤ (43152450481657/100000000000000 : ℝ)^779
        have hw : |(2656160471/5000000000 : ℝ)|=(2656160471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393748701/10000000000 : ℝ)|^1035 ≤ (22016734722539/50000000000000 : ℝ)^779
        have hw : |(5393748701/10000000000 : ℝ)|=(5393748701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266259253/1250000000 : ℝ)|^1035 ≤ (6407040034787/50000000000000 : ℝ)^779
        have hw : |(-266259253/1250000000 : ℝ)|=(266259253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s7_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4372486401/10000000000 : ℝ)*x 0 + (2250479713/5000000000 : ℝ)*x 1 + (4247729287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372486401/10000000000 : ℝ)^1035 ≤ (8329181961119/25000000000000 : ℝ)^779 := by
    have hnat : (4372486401 : ℕ)^1035*25000000000000^779 ≤ 8329181961119^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372486401 10000000000 8329181961119 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250479713/5000000000 : ℝ)^1035 ≤ (34623581133353/100000000000000 : ℝ)^779 := by
    have hnat : (2250479713 : ℕ)^1035*100000000000000^779 ≤ 34623581133353^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250479713 5000000000 34623581133353 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247729287/10000000000 : ℝ)^1035 ≤ (1001865344159/3125000000000 : ℝ)^779 := by
    have hnat : (4247729287 : ℕ)^1035*3125000000000^779 ≤ 1001865344159^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247729287 10000000000 1001865344159 3125000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372486401/10000000000 : ℝ), (2250479713/5000000000 : ℝ), (4247729287/10000000000 : ℝ)] ![(8329181961119/25000000000000 : ℝ), (34623581133353/100000000000000 : ℝ), (1001865344159/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372486401/10000000000 : ℝ)|^1035 ≤ (8329181961119/25000000000000 : ℝ)^779
        have hw : |(4372486401/10000000000 : ℝ)|=(4372486401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250479713/5000000000 : ℝ)|^1035 ≤ (34623581133353/100000000000000 : ℝ)^779
        have hw : |(2250479713/5000000000 : ℝ)|=(2250479713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247729287/10000000000 : ℝ)|^1035 ≤ (1001865344159/3125000000000 : ℝ)^779
        have hw : |(4247729287/10000000000 : ℝ)|=(4247729287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7009/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1127/10000 : ℝ) ^ (8279/2048 : ℝ) ≤ (1470350751060089/10000000000000000000 : ℝ) := by
    have hpowers : (1127/10000 : ℝ)^8279 ≤ (1470350751060089/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1127 : ℕ)^8279*10000000000000000000^2048 ≤ 1470350751060089^2048*10000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1127 10000 1470350751060089 10000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1127/10000 : ℝ)) (X := (1470350751060089/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14027/100000 : ℝ) ^ (8279/2048 : ℝ) ≤ (17807045033137613/50000000000000000000 : ℝ) := by
    have hpowers : (14027/100000 : ℝ)^8279 ≤ (17807045033137613/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14027 : ℕ)^8279*50000000000000000000^2048 ≤ 17807045033137613^2048*100000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14027 100000 17807045033137613 50000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14027/100000 : ℝ)) (X := (17807045033137613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001470350751060089/5000000000000000000 : ℝ) ≤ (250018184232151/250000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (5001470350751060089/5000000000000000000 : ℝ)^2048 ≤ (250018184232151/250000000000000 : ℝ)^8279 := by
      have hnat : (5001470350751060089 : ℕ)^2048*250000000000000^8279 ≤ 250018184232151^8279*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001470350751060089 5000000000000000000 250018184232151 250000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250018184232151/250000000000000 : ℝ)) (X := (5001470350751060089/5000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012579399394219029/25000000000000000000 : ℝ) ≤ (2500311121309247/2500000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (25012579399394219029/25000000000000000000 : ℝ)^2048 ≤ (2500311121309247/2500000000000000 : ℝ)^8279 := by
      have hnat : (25012579399394219029 : ℕ)^2048*2500000000000000^8279 ≤ 2500311121309247^8279*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012579399394219029 25000000000000000000 2500311121309247 2500000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500311121309247/2500000000000000 : ℝ)) (X := (25012579399394219029/25000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017807045033137613/25000000000000000000 : ℝ) ≤ (312555050037123/312500000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (25017807045033137613/25000000000000000000 : ℝ)^2048 ≤ (312555050037123/312500000000000 : ℝ)^8279 := by
      have hnat : (25017807045033137613 : ℕ)^2048*312500000000000^8279 ≤ 312555050037123^8279*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017807045033137613 25000000000000000000 312555050037123 312500000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312555050037123/312500000000000 : ℝ)) (X := (25017807045033137613/25000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1470350751060089/10000000000000000000 : ℝ) ≤ ((689008739089681109/689250000000000000 : ℝ)+2*(129278987737/68925000000000 : ℝ)*(1127/10000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (689008739089681109/689250000000000000 : ℝ)+2*(129278987737/68925000000000 : ℝ)*(1127/10000 : ℝ)=(250018184232151/250000000000000 : ℝ) by norm_num, show 1+2*(1470350751060089/10000000000000000000 : ℝ)=(5001470350751060089/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17807045033137613/50000000000000000000 : ℝ)+(1470350751060089/10000000000000000000 : ℝ) ≤ ((689008739089681109/689250000000000000 : ℝ)+(129278987737/68925000000000 : ℝ)*((14027/100000 : ℝ)+(1127/10000 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (689008739089681109/689250000000000000 : ℝ)+(129278987737/68925000000000 : ℝ)*((14027/100000 : ℝ)+(1127/10000 : ℝ))=(2500311121309247/2500000000000000 : ℝ) by norm_num, show 1+(17807045033137613/50000000000000000000 : ℝ)+(1470350751060089/10000000000000000000 : ℝ)=(25012579399394219029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17807045033137613/50000000000000000000 : ℝ) ≤ ((689008739089681109/689250000000000000 : ℝ)+2*(129278987737/68925000000000 : ℝ)*(14027/100000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (689008739089681109/689250000000000000 : ℝ)+2*(129278987737/68925000000000 : ℝ)*(14027/100000 : ℝ)=(312555050037123/312500000000000 : ℝ) by norm_num, show 1+2*(17807045033137613/50000000000000000000 : ℝ)=(25017807045033137613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (689008739089681109/689250000000000000 : ℝ)*(X 1 0+X 2 0)+(129278987737/68925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (689008739089681109/689250000000000000 : ℝ)) (alpha := (129278987737/68925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (689008739089681109/689250000000000000 : ℝ)*(X 0 1+X 2 1)+(129278987737/68925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (689008739089681109/689250000000000000 : ℝ)) (alpha := (129278987737/68925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (689008739089681109/689250000000000000 : ℝ)*(X 0 2+X 1 2)+(129278987737/68925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14027/100000 : ℝ)) (c := (689008739089681109/689250000000000000 : ℝ)) (alpha := (129278987737/68925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-68545641/312500000 : ℝ)*X 0 0+(2697037317/5000000000 : ℝ)*X 0 1+(2632376249/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672474199/5000000000 : ℝ)*X 1 0+(-2259070127/10000000000 : ℝ)*X 1 1+(5264752731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344948911/10000000000 : ℝ)*X 2 0+(1052950473/2000000000 : ℝ)*X 2 1+(-282383741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27327979/62500000 : ℝ)*X 0 0+(1061772073/2500000000 : ℝ)*X 0 1+(4501597977/10000000000 : ℝ)*X 0 2+(27327979/62500000 : ℝ)*X 1 0+(1061772073/2500000000 : ℝ)*X 1 1+(4501597977/10000000000 : ℝ)*X 1 2+(27327979/62500000 : ℝ)*X 2 0+(1061772073/2500000000 : ℝ)*X 2 1+(4501597977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548366441/2500000000 : ℝ)*X 0 0+(1053015421/2000000000 : ℝ)*X 0 1+(5393748691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106246419/200000000 : ℝ)*X 1 0+(-2130074017/10000000000 : ℝ)*X 1 1+(5393748697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656160471/5000000000 : ℝ)*X 2 0+(5393748701/10000000000 : ℝ)*X 2 1+(-266259253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372486401/10000000000 : ℝ)*X 0 0+(2250479713/5000000000 : ℝ)*X 0 1+(4247729287/10000000000 : ℝ)*X 0 2+(4372486401/10000000000 : ℝ)*X 1 0+(2250479713/5000000000 : ℝ)*X 1 1+(4247729287/10000000000 : ℝ)*X 1 2+(4372486401/10000000000 : ℝ)*X 2 0+(2250479713/5000000000 : ℝ)*X 2 1+(4247729287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3912685899556627851391347/2297500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (376168447/100000000000000 : ℝ)*(base19) + (356871177/50000000000000 : ℝ)*(base23) + (230357193/100000000000000 : ℝ)*(lower2) + (301843/1250000000000 : ℝ)*(lower3) + (1166181873502217/20000000000000 : ℝ)*(major0) + (1166181873502217/20000000000000 : ℝ)*(major1) + (1166181873502217/20000000000000 : ℝ)*(major2) + (3866323164788367/50000000000000 : ℝ)*(sp0) + (7732675601093437/100000000000000 : ℝ)*(sp1) + (3866339792860787/50000000000000 : ℝ)*(sp2) + (1964563996290693/50000000000000 : ℝ)*(sp3) + (16984943597/50000000000000 : ℝ)*(sp4) + (1080550511/25000000000000 : ℝ)*(sp5) + (207724191/2000000000000 : ℝ)*(sp7) + (491142297348867/12500000000000 : ℝ)*(f.failure) + (966585037432991/12500000000000 : ℝ)*(f.sum) + (6410566597373/1378500000000000000000000000 : ℝ)*base66 + (5318521975159551/4595000000000000000000000000000 : ℝ)*base67 + (6497682512259551/4595000000000000000000000000000 : ℝ)*base69 + (60871481159249551/4595000000000000000000000000000 : ℝ)*base71 + (16678466228389/2757000000000000000000000000 : ℝ)*base74 + (105451766128495449/4595000000000000000000000000000 : ℝ)*base76 + (31072813395389551/4595000000000000000000000000000 : ℝ)*base77 + (121319511612320449/4595000000000000000000000000000 : ℝ)*base80 + (1762589601923/344625000000000000000000000 : ℝ)*base82 + (11188777/1250000000000000000000 : ℝ)*base89 + (11188777/1250000000000000000000 : ℝ)*base91 + (11188777/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93607650499971975572063157/11487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399717677/25000000000000 : ℝ)*(base19) + (1697818703/100000000000000 : ℝ)*(base23) + (87186341/50000000000000 : ℝ)*(upper3) + (51480077/100000000000000 : ℝ)*(lower4) + (87653843/50000000000000 : ℝ)*(upper5) + (5860349426745291/100000000000000 : ℝ)*(major0) + (5860349426745291/100000000000000 : ℝ)*(major1) + (5860349426745291/100000000000000 : ℝ)*(major2) + (21968531113/50000000000000 : ℝ)*(sp1) + (23087105401/50000000000000 : ℝ)*(sp2) + (7771722119629777/100000000000000 : ℝ)*(sp4) + (7771676583696843/100000000000000 : ℝ)*(sp5) + (485729640475017/6250000000000 : ℝ)*(sp6) + (987244115559759/25000000000000 : ℝ)*(sp7) + (987244115559759/25000000000000 : ℝ)*(f.failure) + (7771722119629777/100000000000000 : ℝ)*(f.sum) + (9560195745201/1148750000000000000000000000 : ℝ)*base66 + (28306833819282427/22975000000000000000000000000000 : ℝ)*base68 + (85057618375332427/22975000000000000000000000000000 : ℝ)*base70 + (6646355635457427/22975000000000000000000000000000 : ℝ)*base72 + (1016565079671/4595000000000000000000000000 : ℝ)*base73 + (308520070113582427/22975000000000000000000000000000 : ℝ)*base76 + (131218139288257427/22975000000000000000000000000000 : ℝ)*base78 + (59238945164857427/22975000000000000000000000000000 : ℝ)*base80 + (710090986737/574375000000000000000000000 : ℝ)*base81 + (5457171/2500000000000000000000 : ℝ)*base90 + (5457171/2500000000000000000000 : ℝ)*base92 + (5457171/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1087_s8_0 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193467691/10000000000 : ℝ)*x 0 + (1348495117/2500000000 : ℝ)*x 1 + (2632421017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193467691/10000000000 : ℝ)^1035 ≤ (3330807648679/25000000000000 : ℝ)^779 := by
    have hnat : (2193467691 : ℕ)^1035*25000000000000^779 ≤ 3330807648679^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193467691 10000000000 3330807648679 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348495117/2500000000 : ℝ)^1035 ≤ (22017991677623/50000000000000 : ℝ)^779 := by
    have hnat : (1348495117 : ℕ)^1035*50000000000000^779 ≤ 22017991677623^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348495117 2500000000 22017991677623 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632421017/5000000000 : ℝ)^1035 ≤ (2665049127443/6250000000000 : ℝ)^779 := by
    have hnat : (2632421017 : ℕ)^1035*6250000000000^779 ≤ 2665049127443^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632421017 5000000000 2665049127443 6250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193467691/10000000000 : ℝ), (1348495117/2500000000 : ℝ), (2632421017/5000000000 : ℝ)] ![(3330807648679/25000000000000 : ℝ), (22017991677623/50000000000000 : ℝ), (2665049127443/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193467691/10000000000 : ℝ)|^1035 ≤ (3330807648679/25000000000000 : ℝ)^779
        have hw : |(-2193467691/10000000000 : ℝ)|=(2193467691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348495117/2500000000 : ℝ)|^1035 ≤ (22017991677623/50000000000000 : ℝ)^779
        have hw : |(1348495117/2500000000 : ℝ)|=(1348495117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632421017/5000000000 : ℝ)|^1035 ≤ (2665049127443/6250000000000 : ℝ)^779
        have hw : |(2632421017/5000000000 : ℝ)|=(2632421017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_1 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344925297/10000000000 : ℝ)*x 0 + (-451796437/2000000000 : ℝ)*x 1 + (5264842541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344925297/10000000000 : ℝ)^1035 ≤ (21752344488349/50000000000000 : ℝ)^779 := by
    have hnat : (5344925297 : ℕ)^1035*50000000000000^779 ≤ 21752344488349^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344925297 10000000000 21752344488349 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451796437/2000000000 : ℝ)^1035 ≤ (6927259758139/50000000000000 : ℝ)^779 := by
    have hnat : (451796437 : ℕ)^1035*50000000000000^779 ≤ 6927259758139^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451796437 2000000000 6927259758139 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264842541/10000000000 : ℝ)^1035 ≤ (42640791494791/100000000000000 : ℝ)^779 := by
    have hnat : (5264842541 : ℕ)^1035*100000000000000^779 ≤ 42640791494791^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264842541 10000000000 42640791494791 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344925297/10000000000 : ℝ), (-451796437/2000000000 : ℝ), (5264842541/10000000000 : ℝ)] ![(21752344488349/50000000000000 : ℝ), (6927259758139/50000000000000 : ℝ), (42640791494791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344925297/10000000000 : ℝ)|^1035 ≤ (21752344488349/50000000000000 : ℝ)^779
        have hw : |(5344925297/10000000000 : ℝ)|=(5344925297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451796437/2000000000 : ℝ)|^1035 ≤ (6927259758139/50000000000000 : ℝ)^779
        have hw : |(-451796437/2000000000 : ℝ)|=(451796437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264842541/10000000000 : ℝ)|^1035 ≤ (42640791494791/100000000000000 : ℝ)^779
        have hw : |(5264842541/10000000000 : ℝ)|=(5264842541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_2 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672462547/5000000000 : ℝ)*x 0 + (5264842617/10000000000 : ℝ)*x 1 + (-1129491177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672462547/5000000000 : ℝ)^1035 ≤ (43504686781401/100000000000000 : ℝ)^779 := by
    have hnat : (2672462547 : ℕ)^1035*100000000000000^779 ≤ 43504686781401^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672462547 5000000000 43504686781401 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264842617/10000000000 : ℝ)^1035 ≤ (1332524759769/3125000000000 : ℝ)^779 := by
    have hnat : (5264842617 : ℕ)^1035*3125000000000^779 ≤ 1332524759769^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264842617 10000000000 1332524759769 3125000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129491177/5000000000 : ℝ)^1035 ≤ (13854520893387/100000000000000 : ℝ)^779 := by
    have hnat : (1129491177 : ℕ)^1035*100000000000000^779 ≤ 13854520893387^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129491177 5000000000 13854520893387 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672462547/5000000000 : ℝ), (5264842617/10000000000 : ℝ), (-1129491177/5000000000 : ℝ)] ![(43504686781401/100000000000000 : ℝ), (1332524759769/3125000000000 : ℝ), (13854520893387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672462547/5000000000 : ℝ)|^1035 ≤ (43504686781401/100000000000000 : ℝ)^779
        have hw : |(2672462547/5000000000 : ℝ)|=(2672462547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264842617/10000000000 : ℝ)|^1035 ≤ (1332524759769/3125000000000 : ℝ)^779
        have hw : |(5264842617/10000000000 : ℝ)|=(5264842617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1129491177/5000000000 : ℝ)|^1035 ≤ (13854520893387/100000000000000 : ℝ)^779
        have hw : |(-1129491177/5000000000 : ℝ)|=(1129491177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_3 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (218624059/500000000 : ℝ)*x 0 + (4247268449/10000000000 : ℝ)*x 1 + (1125354183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218624059/500000000 : ℝ)^1035 ≤ (33316674988953/100000000000000 : ℝ)^779 := by
    have hnat : (218624059 : ℕ)^1035*100000000000000^779 ≤ 33316674988953^779*500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218624059 500000000 33316674988953 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247268449/10000000000 : ℝ)^1035 ≤ (6411013981409/20000000000000 : ℝ)^779 := by
    have hnat : (4247268449 : ℕ)^1035*20000000000000^779 ≤ 6411013981409^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247268449 10000000000 6411013981409 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125354183/2500000000 : ℝ)^1035 ≤ (17314127540959/50000000000000 : ℝ)^779 := by
    have hnat : (1125354183 : ℕ)^1035*50000000000000^779 ≤ 17314127540959^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125354183 2500000000 17314127540959 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218624059/500000000 : ℝ), (4247268449/10000000000 : ℝ), (1125354183/2500000000 : ℝ)] ![(33316674988953/100000000000000 : ℝ), (6411013981409/20000000000000 : ℝ), (17314127540959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218624059/500000000 : ℝ)|^1035 ≤ (33316674988953/100000000000000 : ℝ)^779
        have hw : |(218624059/500000000 : ℝ)|=(218624059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247268449/10000000000 : ℝ)|^1035 ≤ (6411013981409/20000000000000 : ℝ)^779
        have hw : |(4247268449/10000000000 : ℝ)|=(4247268449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125354183/2500000000 : ℝ)|^1035 ≤ (17314127540959/50000000000000 : ℝ)^779
        have hw : |(1125354183/2500000000 : ℝ)|=(1125354183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_4 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193472623/10000000000 : ℝ)*x 0 + (5265165921/10000000000 : ℝ)*x 1 + (5393655473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193472623/10000000000 : ℝ)^1035 ≤ (52044024987/390625000000 : ℝ)^779 := by
    have hnat : (2193472623 : ℕ)^1035*390625000000^779 ≤ 52044024987^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193472623 10000000000 52044024987 390625000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265165921/10000000000 : ℝ)^1035 ≤ (8528854268603/20000000000000 : ℝ)^779 := by
    have hnat : (5265165921 : ℕ)^1035*20000000000000^779 ≤ 8528854268603^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265165921 10000000000 8528854268603 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393655473/10000000000 : ℝ)^1035 ≤ (11008114559429/25000000000000 : ℝ)^779 := by
    have hnat : (5393655473 : ℕ)^1035*25000000000000^779 ≤ 11008114559429^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393655473 10000000000 11008114559429 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193472623/10000000000 : ℝ), (5265165921/10000000000 : ℝ), (5393655473/10000000000 : ℝ)] ![(52044024987/390625000000 : ℝ), (8528854268603/20000000000000 : ℝ), (11008114559429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193472623/10000000000 : ℝ)|^1035 ≤ (52044024987/390625000000 : ℝ)^779
        have hw : |(-2193472623/10000000000 : ℝ)|=(2193472623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265165921/10000000000 : ℝ)|^1035 ≤ (8528854268603/20000000000000 : ℝ)^779
        have hw : |(5265165921/10000000000 : ℝ)|=(5265165921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393655473/10000000000 : ℝ)|^1035 ≤ (11008114559429/25000000000000 : ℝ)^779
        have hw : |(5393655473/10000000000 : ℝ)|=(5393655473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_5 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656172123/5000000000 : ℝ)*x 0 + (-2130168963/10000000000 : ℝ)*x 1 + (21068967/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656172123/5000000000 : ℝ)^1035 ≤ (10788175497853/25000000000000 : ℝ)^779 := by
    have hnat : (2656172123 : ℕ)^1035*25000000000000^779 ≤ 10788175497853^779*5000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656172123 5000000000 10788175497853 25000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130168963/10000000000 : ℝ)^1035 ≤ (512593555911/4000000000000 : ℝ)^779 := by
    have hnat : (2130168963 : ℕ)^1035*4000000000000^779 ≤ 512593555911^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130168963 10000000000 512593555911 4000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21068967/39062500 : ℝ)^1035 ≤ (8806491818919/20000000000000 : ℝ)^779 := by
    have hnat : (21068967 : ℕ)^1035*20000000000000^779 ≤ 8806491818919^779*39062500^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21068967 39062500 8806491818919 20000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656172123/5000000000 : ℝ), (-2130168963/10000000000 : ℝ), (21068967/39062500 : ℝ)] ![(10788175497853/25000000000000 : ℝ), (512593555911/4000000000000 : ℝ), (8806491818919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656172123/5000000000 : ℝ)|^1035 ≤ (10788175497853/25000000000000 : ℝ)^779
        have hw : |(2656172123/5000000000 : ℝ)|=(2656172123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130168963/10000000000 : ℝ)|^1035 ≤ (512593555911/4000000000000 : ℝ)^779
        have hw : |(-2130168963/10000000000 : ℝ)|=(2130168963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21068967/39062500 : ℝ)|^1035 ≤ (8806491818919/20000000000000 : ℝ)^779
        have hw : |(21068967/39062500 : ℝ)|=(21068967/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_6 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312343853/10000000000 : ℝ)*x 0 + (1078731113/2000000000 : ℝ)*x 1 + (-532542369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312343853/10000000000 : ℝ)^1035 ≤ (21576348874967/50000000000000 : ℝ)^779 := by
    have hnat : (5312343853 : ℕ)^1035*50000000000000^779 ≤ 21576348874967^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312343853 10000000000 21576348874967 50000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078731113/2000000000 : ℝ)^1035 ≤ (110081148089/250000000000 : ℝ)^779 := by
    have hnat : (1078731113 : ℕ)^1035*250000000000^779 ≤ 110081148089^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078731113 2000000000 110081148089 250000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532542369/2500000000 : ℝ)^1035 ≤ (12814842998111/100000000000000 : ℝ)^779 := by
    have hnat : (532542369 : ℕ)^1035*100000000000000^779 ≤ 12814842998111^779*2500000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532542369 2500000000 12814842998111 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312343853/10000000000 : ℝ), (1078731113/2000000000 : ℝ), (-532542369/2500000000 : ℝ)] ![(21576348874967/50000000000000 : ℝ), (110081148089/250000000000 : ℝ), (12814842998111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312343853/10000000000 : ℝ)|^1035 ≤ (21576348874967/50000000000000 : ℝ)^779
        have hw : |(5312343853/10000000000 : ℝ)|=(5312343853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078731113/2000000000 : ℝ)|^1035 ≤ (110081148089/250000000000 : ℝ)^779
        have hw : |(1078731113/2000000000 : ℝ)|=(1078731113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532542369/2500000000 : ℝ)|^1035 ≤ (12814842998111/100000000000000 : ℝ)^779
        have hw : |(-532542369/2500000000 : ℝ)|=(532542369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1087_s8_7 (p : ℝ) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4372490801/10000000000 : ℝ)*x 0 + (900155923/2000000000 : ℝ)*x 1 + (4247908107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372490801/10000000000 : ℝ)^1035 ≤ (33316772388507/100000000000000 : ℝ)^779 := by
    have hnat : (4372490801 : ℕ)^1035*100000000000000^779 ≤ 33316772388507^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372490801 10000000000 33316772388507 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900155923/2000000000 : ℝ)^1035 ≤ (34621743397091/100000000000000 : ℝ)^779 := by
    have hnat : (900155923 : ℕ)^1035*100000000000000^779 ≤ 34621743397091^779*2000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900155923 2000000000 34621743397091 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247908107/10000000000 : ℝ)^1035 ≤ (32061484195573/100000000000000 : ℝ)^779 := by
    have hnat : (4247908107 : ℕ)^1035*100000000000000^779 ≤ 32061484195573^779*10000000000^1035 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247908107 10000000000 32061484195573 100000000000000 1035 779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1035/256 : ℝ)) 1035 779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372490801/10000000000 : ℝ), (900155923/2000000000 : ℝ), (4247908107/10000000000 : ℝ)] ![(33316772388507/100000000000000 : ℝ), (34621743397091/100000000000000 : ℝ), (32061484195573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372490801/10000000000 : ℝ)|^1035 ≤ (33316772388507/100000000000000 : ℝ)^779
        have hw : |(4372490801/10000000000 : ℝ)|=(4372490801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900155923/2000000000 : ℝ)|^1035 ≤ (34621743397091/100000000000000 : ℝ)^779
        have hw : |(900155923/2000000000 : ℝ)|=(900155923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247908107/10000000000 : ℝ)|^1035 ≤ (32061484195573/100000000000000 : ℝ)^779
        have hw : |(4247908107/10000000000 : ℝ)|=(4247908107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1087_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (141/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (438/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (8279/2048 : ℝ) ≤ (7375515867223561/50000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^8279 ≤ (7375515867223561/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11279 : ℕ)^8279*50000000000000000000^2048 ≤ 7375515867223561^2048*100000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 7375515867223561 50000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (7375515867223561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7009/50000 : ℝ) ^ (8279/2048 : ℝ) ≤ (35521806668323203/100000000000000000000 : ℝ) := by
    have hpowers : (7009/50000 : ℝ)^8279 ≤ (35521806668323203/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7009 : ℕ)^8279*100000000000000000000^2048 ≤ 35521806668323203^2048*50000^8279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7009 50000 35521806668323203 100000000000000000000 8279 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7009/50000 : ℝ)) (X := (35521806668323203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007375515867223561/25000000000000000000 : ℝ) ≤ (2000145944001137/2000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (25007375515867223561/25000000000000000000 : ℝ)^2048 ≤ (2000145944001137/2000000000000000 : ℝ)^8279 := by
      have hnat : (25007375515867223561 : ℕ)^2048*2000000000000000^8279 ≤ 2000145944001137^8279*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007375515867223561 25000000000000000000 2000145944001137 2000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000145944001137/2000000000000000 : ℝ)) (X := (25007375515867223561/25000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002010913536110813/4000000000000000000 : ℝ) ≤ (2000248675687077/2000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (4002010913536110813/4000000000000000000 : ℝ)^2048 ≤ (2000248675687077/2000000000000000 : ℝ)^8279 := by
      have hnat : (4002010913536110813 : ℕ)^2048*2000000000000000^8279 ≤ 2000248675687077^8279*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002010913536110813 4000000000000000000 2000248675687077 2000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000248675687077/2000000000000000 : ℝ)) (X := (4002010913536110813/4000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035521806668323203/50000000000000000000 : ℝ) ≤ (2000351407373017/2000000000000000 : ℝ) ^ (8279/2048 : ℝ) := by
    have hpowers : (50035521806668323203/50000000000000000000 : ℝ)^2048 ≤ (2000351407373017/2000000000000000 : ℝ)^8279 := by
      have hnat : (50035521806668323203 : ℕ)^2048*2000000000000000^8279 ≤ 2000351407373017^8279*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035521806668323203 50000000000000000000 2000351407373017 2000000000000000 2048 8279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000351407373017/2000000000000000 : ℝ)) (X := (50035521806668323203/50000000000000000000 : ℝ)) (by norm_num) 8279 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7375515867223561/50000000000000000000 : ℝ) ≤ ((5476082319247679723/5478000000000000000 : ℝ)+2*(5136584297/2739000000000 : ℝ)*(11279/100000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (5476082319247679723/5478000000000000000 : ℝ)+2*(5136584297/2739000000000 : ℝ)*(11279/100000 : ℝ)=(2000145944001137/2000000000000000 : ℝ) by norm_num, show 1+2*(7375515867223561/50000000000000000000 : ℝ)=(25007375515867223561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35521806668323203/100000000000000000000 : ℝ)+(7375515867223561/50000000000000000000 : ℝ) ≤ ((5476082319247679723/5478000000000000000 : ℝ)+(5136584297/2739000000000 : ℝ)*((7009/50000 : ℝ)+(11279/100000 : ℝ)))^(8279/2048 : ℝ) := by
    rw [show (5476082319247679723/5478000000000000000 : ℝ)+(5136584297/2739000000000 : ℝ)*((7009/50000 : ℝ)+(11279/100000 : ℝ))=(2000248675687077/2000000000000000 : ℝ) by norm_num, show 1+(35521806668323203/100000000000000000000 : ℝ)+(7375515867223561/50000000000000000000 : ℝ)=(4002010913536110813/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35521806668323203/100000000000000000000 : ℝ) ≤ ((5476082319247679723/5478000000000000000 : ℝ)+2*(5136584297/2739000000000 : ℝ)*(7009/50000 : ℝ))^(8279/2048 : ℝ) := by
    rw [show (5476082319247679723/5478000000000000000 : ℝ)+2*(5136584297/2739000000000 : ℝ)*(7009/50000 : ℝ)=(2000351407373017/2000000000000000 : ℝ) by norm_num, show 1+2*(35521806668323203/100000000000000000000 : ℝ)=(50035521806668323203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5476082319247679723/5478000000000000000 : ℝ)*(X 1 0+X 2 0)+(5136584297/2739000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (5476082319247679723/5478000000000000000 : ℝ)) (alpha := (5136584297/2739000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5476082319247679723/5478000000000000000 : ℝ)*(X 0 1+X 2 1)+(5136584297/2739000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (5476082319247679723/5478000000000000000 : ℝ)) (alpha := (5136584297/2739000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5476082319247679723/5478000000000000000 : ℝ)*(X 0 2+X 1 2)+(5136584297/2739000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8279/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (5476082319247679723/5478000000000000000 : ℝ)) (alpha := (5136584297/2739000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2193467691/10000000000 : ℝ)*X 0 0+(1348495117/2500000000 : ℝ)*X 0 1+(2632421017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344925297/10000000000 : ℝ)*X 1 0+(-451796437/2000000000 : ℝ)*X 1 1+(5264842541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672462547/5000000000 : ℝ)*X 2 0+(5264842617/10000000000 : ℝ)*X 2 1+(-1129491177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218624059/500000000 : ℝ)*X 0 0+(4247268449/10000000000 : ℝ)*X 0 1+(1125354183/2500000000 : ℝ)*X 0 2+(218624059/500000000 : ℝ)*X 1 0+(4247268449/10000000000 : ℝ)*X 1 1+(1125354183/2500000000 : ℝ)*X 1 2+(218624059/500000000 : ℝ)*X 2 0+(4247268449/10000000000 : ℝ)*X 2 1+(1125354183/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2193472623/10000000000 : ℝ)*X 0 0+(5265165921/10000000000 : ℝ)*X 0 1+(5393655473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656172123/5000000000 : ℝ)*X 1 0+(-2130168963/10000000000 : ℝ)*X 1 1+(21068967/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312343853/10000000000 : ℝ)*X 2 0+(1078731113/2000000000 : ℝ)*X 2 1+(-532542369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372490801/10000000000 : ℝ)*X 0 0+(900155923/2000000000 : ℝ)*X 0 1+(4247908107/10000000000 : ℝ)*X 0 2+(4372490801/10000000000 : ℝ)*X 1 0+(900155923/2000000000 : ℝ)*X 1 1+(4247908107/10000000000 : ℝ)*X 1 2+(4372490801/10000000000 : ℝ)*X 2 0+(900155923/2000000000 : ℝ)*X 2 1+(4247908107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1087_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (504227796406613036750349309/45650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1029586037/50000000000000 : ℝ)*(base19) + (35113619/2000000000000 : ℝ)*(base23) + (218129611/50000000000000 : ℝ)*(upper3) + (1253703/25000000000000 : ℝ)*(upper4) + (6652861/6250000000000 : ℝ)*(upper5) + (5839287946320183/100000000000000 : ℝ)*(major0) + (5839287946320183/100000000000000 : ℝ)*(major1) + (5839287946320183/100000000000000 : ℝ)*(major2) + (3871859481349643/50000000000000 : ℝ)*(sp0) + (7743789209755637/100000000000000 : ℝ)*(sp1) + (3871894756623381/50000000000000 : ℝ)*(sp2) + (24592155472897/625000000000 : ℝ)*(sp3) + (36153114213/50000000000000 : ℝ)*(sp4) + (39379865267/100000000000000 : ℝ)*(sp7) + (3934784255528787/100000000000000 : ℝ)*(f.failure) + (7743791268927711/100000000000000 : ℝ)*(f.sum) + (425130818119/913000000000000000000000000 : ℝ)*base66 + (107175103860183103/182600000000000000000000000000000 : ℝ)*base67 + (1607670898935016897/182600000000000000000000000000000 : ℝ)*base70 + (98082411220016897/182600000000000000000000000000000 : ℝ)*base72 + (141906903521/45650000000000000000000000 : ℝ)*base73 + (3246412845062016897/182600000000000000000000000000000 : ℝ)*base76 + (141613600981416897/182600000000000000000000000000000 : ℝ)*base78 + (4413387352835816897/182600000000000000000000000000000 : ℝ)*base80 + (1518070352553/913000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (11130297/10000000000000000000000 : ℝ)*base89 + (11130297/10000000000000000000000 : ℝ)*base91 + (11130297/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25312140658570979574327519/2853125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1705828213/100000000000000 : ℝ)*(base19) + (249560721/25000000000000 : ℝ)*(base23) + (34009513/12500000000000 : ℝ)*(lower1) + (11018531/20000000000000 : ℝ)*(upper2) + (80470591/100000000000000 : ℝ)*(upper3) + (107619509/50000000000000 : ℝ)*(upper5) + (91697413820211/1562500000000 : ℝ)*(major0) + (91697413820211/1562500000000 : ℝ)*(major1) + (91697413820211/1562500000000 : ℝ)*(major2) + (19202250657/50000000000000 : ℝ)*(sp1) + (7782709353133659/100000000000000 : ℝ)*(sp4) + (7782669242804133/100000000000000 : ℝ)*(sp5) + (311308334195631/4000000000000 : ℝ)*(sp6) + (3954559320129159/100000000000000 : ℝ)*(sp7) + (3954559320129159/100000000000000 : ℝ)*(f.failure) + (7782709353133659/100000000000000 : ℝ)*(f.sum) + (484487910847/456500000000000000000000000 : ℝ)*base65 + (27094064131431351/2853125000000000000000000000000 : ℝ)*base67 + (176220562035281149/2853125000000000000000000000000 : ℝ)*base70 + (319453697740247/356640625000000000000000000000 : ℝ)*base71 + (227095050189/114125000000000000000000000 : ℝ)*base73 + (8573562875222253/356640625000000000000000000000 : ℝ)*base76 + (12993082390087601/2853125000000000000000000000000 : ℝ)*base77 + (62412676145281351/2853125000000000000000000000000 : ℝ)*base79 + (32813082629249/913000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (60825771/10000000000000000000000 : ℝ)*base90 + (60825771/10000000000000000000000 : ℝ)*base92 + (60825771/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1087_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1087_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1087_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1087_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1087_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1087_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8279/2048 : ℝ) ≤ p) (hpb : p ≤ (1035/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148401731/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (141/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1087_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
