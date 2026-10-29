-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:36.007011+00:00
-- url     : https://prove2.me/submissions/eeccef9c-5131-48ec-b0c8-b291982124b2

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
theorem support_rectangle_w1710_s0_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-668295493/5000000000 : ℝ)*x 0 + (5697849757/10000000000 : ℝ)*x 1 + (620025649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668295493/5000000000 : ℝ)^5303 ≤ (2064347350211/25000000000000 : ℝ)^4279 := by
    have hnat : (668295493 : ℕ)^5303*25000000000000^4279 ≤ 2064347350211^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668295493 5000000000 2064347350211 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5697849757/10000000000 : ℝ)^5303 ≤ (24901219881553/50000000000000 : ℝ)^4279 := by
    have hnat : (5697849757 : ℕ)^5303*50000000000000^4279 ≤ 24901219881553^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5697849757 10000000000 24901219881553 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (620025649/1250000000 : ℝ)^5303 ≤ (5242521353487/12500000000000 : ℝ)^4279 := by
    have hnat : (620025649 : ℕ)^5303*12500000000000^4279 ≤ 5242521353487^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620025649 1250000000 5242521353487 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-668295493/5000000000 : ℝ), (5697849757/10000000000 : ℝ), (620025649/1250000000 : ℝ)] ![(2064347350211/25000000000000 : ℝ), (24901219881553/50000000000000 : ℝ), (5242521353487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-668295493/5000000000 : ℝ)|^5303 ≤ (2064347350211/25000000000000 : ℝ)^4279
        have hw : |(-668295493/5000000000 : ℝ)|=(668295493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5697849757/10000000000 : ℝ)|^5303 ≤ (24901219881553/50000000000000 : ℝ)^4279
        have hw : |(5697849757/10000000000 : ℝ)|=(5697849757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(620025649/1250000000 : ℝ)|^5303 ≤ (5242521353487/12500000000000 : ℝ)^4279
        have hw : |(620025649/1250000000 : ℝ)|=(620025649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2702137507/5000000000 : ℝ)*x 0 + (-868011631/5000000000 : ℝ)*x 1 + (49602049/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702137507/5000000000 : ℝ)^5303 ≤ (2915139375781/6250000000000 : ℝ)^4279 := by
    have hnat : (2702137507 : ℕ)^5303*6250000000000^4279 ≤ 2915139375781^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702137507 5000000000 2915139375781 6250000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868011631/5000000000 : ℝ)^5303 ≤ (1141760219913/10000000000000 : ℝ)^4279 := by
    have hnat : (868011631 : ℕ)^5303*10000000000000^4279 ≤ 1141760219913^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868011631 5000000000 1141760219913 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49602049/100000000 : ℝ)^5303 ≤ (20970083884049/50000000000000 : ℝ)^4279 := by
    have hnat : (49602049 : ℕ)^5303*50000000000000^4279 ≤ 20970083884049^4279*100000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49602049 100000000 20970083884049 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702137507/5000000000 : ℝ), (-868011631/5000000000 : ℝ), (49602049/100000000 : ℝ)] ![(2915139375781/6250000000000 : ℝ), (1141760219913/10000000000000 : ℝ), (20970083884049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702137507/5000000000 : ℝ)|^5303 ≤ (2915139375781/6250000000000 : ℝ)^4279
        have hw : |(2702137507/5000000000 : ℝ)|=(2702137507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-868011631/5000000000 : ℝ)|^5303 ≤ (1141760219913/10000000000000 : ℝ)^4279
        have hw : |(-868011631/5000000000 : ℝ)|=(868011631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49602049/100000000 : ℝ)|^5303 ≤ (20970083884049/50000000000000 : ℝ)^4279
        have hw : |(49602049/100000000 : ℝ)|=(49602049/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2702137413/5000000000 : ℝ)*x 0 + (155006407/312500000 : ℝ)*x 1 + (-34720467/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702137413/5000000000 : ℝ)^5303 ≤ (46642228001649/100000000000000 : ℝ)^4279 := by
    have hnat : (2702137413 : ℕ)^5303*100000000000000^4279 ≤ 46642228001649^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702137413 5000000000 46642228001649 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155006407/312500000 : ℝ)^5303 ≤ (5242521133433/12500000000000 : ℝ)^4279 := by
    have hnat : (155006407 : ℕ)^5303*12500000000000^4279 ≤ 5242521133433^4279*312500000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155006407 312500000 5242521133433 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34720467/200000000 : ℝ)^5303 ≤ (5708801458199/50000000000000 : ℝ)^4279 := by
    have hnat : (34720467 : ℕ)^5303*50000000000000^4279 ≤ 5708801458199^4279*200000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34720467 200000000 5708801458199 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702137413/5000000000 : ℝ), (155006407/312500000 : ℝ), (-34720467/200000000 : ℝ)] ![(46642228001649/100000000000000 : ℝ), (5242521133433/12500000000000 : ℝ), (5708801458199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702137413/5000000000 : ℝ)|^5303 ≤ (46642228001649/100000000000000 : ℝ)^4279
        have hw : |(2702137413/5000000000 : ℝ)|=(2702137413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155006407/312500000 : ℝ)|^5303 ≤ (5242521133433/12500000000000 : ℝ)^4279
        have hw : |(155006407/312500000 : ℝ)|=(155006407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34720467/200000000 : ℝ)|^5303 ≤ (5708801458199/50000000000000 : ℝ)^4279
        have hw : |(-34720467/200000000 : ℝ)|=(34720467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4039569441/10000000000 : ℝ)*x 0 + (3059012633/10000000000 : ℝ)*x 1 + (5197615233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039569441/10000000000 : ℝ)^5303 ≤ (16259149303889/50000000000000 : ℝ)^4279 := by
    have hnat : (4039569441 : ℕ)^5303*50000000000000^4279 ≤ 16259149303889^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039569441 10000000000 16259149303889 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059012633/10000000000 : ℝ)^5303 ≤ (23039689653787/100000000000000 : ℝ)^4279 := by
    have hnat : (3059012633 : ℕ)^5303*100000000000000^4279 ≤ 23039689653787^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059012633 10000000000 23039689653787 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5197615233/10000000000 : ℝ)^5303 ≤ (5555251464999/12500000000000 : ℝ)^4279 := by
    have hnat : (5197615233 : ℕ)^5303*12500000000000^4279 ≤ 5555251464999^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197615233 10000000000 5555251464999 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039569441/10000000000 : ℝ), (3059012633/10000000000 : ℝ), (5197615233/10000000000 : ℝ)] ![(16259149303889/50000000000000 : ℝ), (23039689653787/100000000000000 : ℝ), (5555251464999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039569441/10000000000 : ℝ)|^5303 ≤ (16259149303889/50000000000000 : ℝ)^4279
        have hw : |(4039569441/10000000000 : ℝ)|=(4039569441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059012633/10000000000 : ℝ)|^5303 ≤ (23039689653787/100000000000000 : ℝ)^4279
        have hw : |(3059012633/10000000000 : ℝ)|=(3059012633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5197615233/10000000000 : ℝ)|^5303 ≤ (5555251464999/12500000000000 : ℝ)^4279
        have hw : |(5197615233/10000000000 : ℝ)|=(5197615233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1338261313/10000000000 : ℝ)*x 0 + (995666417/2000000000 : ℝ)*x 1 + (22184057/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338261313/10000000000 : ℝ)^5303 ≤ (4135089986831/50000000000000 : ℝ)^4279 := by
    have hnat : (1338261313 : ℕ)^5303*50000000000000^4279 ≤ 4135089986831^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338261313 10000000000 4135089986831 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995666417/2000000000 : ℝ)^5303 ≤ (21065100585367/50000000000000 : ℝ)^4279 := by
    have hnat : (995666417 : ℕ)^5303*50000000000000^4279 ≤ 21065100585367^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995666417 2000000000 21065100585367 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22184057/39062500 : ℝ)^5303 ≤ (12399904710739/25000000000000 : ℝ)^4279 := by
    have hnat : (22184057 : ℕ)^5303*25000000000000^4279 ≤ 12399904710739^4279*39062500^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22184057 39062500 12399904710739 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1338261313/10000000000 : ℝ), (995666417/2000000000 : ℝ), (22184057/39062500 : ℝ)] ![(4135089986831/50000000000000 : ℝ), (21065100585367/50000000000000 : ℝ), (12399904710739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1338261313/10000000000 : ℝ)|^5303 ≤ (4135089986831/50000000000000 : ℝ)^4279
        have hw : |(-1338261313/10000000000 : ℝ)|=(1338261313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(995666417/2000000000 : ℝ)|^5303 ≤ (21065100585367/50000000000000 : ℝ)^4279
        have hw : |(995666417/2000000000 : ℝ)|=(995666417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22184057/39062500 : ℝ)|^5303 ≤ (12399904710739/25000000000000 : ℝ)^4279
        have hw : |(22184057/39062500 : ℝ)|=(22184057/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_5 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204440731/10000000000 : ℝ)*x 0 + (-508554603/5000000000 : ℝ)*x 1 + (2839559331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204440731/10000000000 : ℝ)^5303 ≤ (11128587637479/25000000000000 : ℝ)^4279 := by
    have hnat : (5204440731 : ℕ)^5303*25000000000000^4279 ≤ 11128587637479^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204440731 10000000000 11128587637479 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508554603/5000000000 : ℝ)^5303 ≤ (5886029840461/100000000000000 : ℝ)^4279 := by
    have hnat : (508554603 : ℕ)^5303*100000000000000^4279 ≤ 5886029840461^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508554603 5000000000 5886029840461 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2839559331/5000000000 : ℝ)^5303 ≤ (49599619600617/100000000000000 : ℝ)^4279 := by
    have hnat : (2839559331 : ℕ)^5303*100000000000000^4279 ≤ 49599619600617^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839559331 5000000000 49599619600617 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204440731/10000000000 : ℝ), (-508554603/5000000000 : ℝ), (2839559331/5000000000 : ℝ)] ![(11128587637479/25000000000000 : ℝ), (5886029840461/100000000000000 : ℝ), (49599619600617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204440731/10000000000 : ℝ)|^5303 ≤ (11128587637479/25000000000000 : ℝ)^4279
        have hw : |(5204440731/10000000000 : ℝ)|=(5204440731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508554603/5000000000 : ℝ)|^5303 ≤ (5886029840461/100000000000000 : ℝ)^4279
        have hw : |(-508554603/5000000000 : ℝ)|=(508554603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2839559331/5000000000 : ℝ)|^5303 ≤ (49599619600617/100000000000000 : ℝ)^4279
        have hw : |(2839559331/5000000000 : ℝ)|=(2839559331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_6 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602220181/5000000000 : ℝ)*x 0 + (5679119437/10000000000 : ℝ)*x 1 + (-508554291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602220181/5000000000 : ℝ)^5303 ≤ (44514346638521/100000000000000 : ℝ)^4279 := by
    have hnat : (2602220181 : ℕ)^5303*100000000000000^4279 ≤ 44514346638521^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602220181 5000000000 44514346638521 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679119437/10000000000 : ℝ)^5303 ≤ (12399906997251/25000000000000 : ℝ)^4279 := by
    have hnat : (5679119437 : ℕ)^5303*25000000000000^4279 ≤ 12399906997251^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679119437 10000000000 12399906997251 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508554291/5000000000 : ℝ)^5303 ≤ (1177205073039/20000000000000 : ℝ)^4279 := by
    have hnat : (508554291 : ℕ)^5303*20000000000000^4279 ≤ 1177205073039^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508554291 5000000000 1177205073039 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602220181/5000000000 : ℝ), (5679119437/10000000000 : ℝ), (-508554291/5000000000 : ℝ)] ![(44514346638521/100000000000000 : ℝ), (12399906997251/25000000000000 : ℝ), (1177205073039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602220181/5000000000 : ℝ)|^5303 ≤ (44514346638521/100000000000000 : ℝ)^4279
        have hw : |(2602220181/5000000000 : ℝ)|=(2602220181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679119437/10000000000 : ℝ)|^5303 ≤ (12399906997251/25000000000000 : ℝ)^4279
        have hw : |(5679119437/10000000000 : ℝ)|=(5679119437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508554291/5000000000 : ℝ)|^5303 ≤ (1177205073039/20000000000000 : ℝ)^4279
        have hw : |(-508554291/5000000000 : ℝ)|=(508554291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s0_7 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (202220399/500000000 : ℝ)*x 0 + (5145060719/10000000000 : ℝ)*x 1 + (389164517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202220399/500000000 : ℝ)^5303 ≤ (32566576526911/100000000000000 : ℝ)^4279 := by
    have hnat : (202220399 : ℕ)^5303*100000000000000^4279 ≤ 32566576526911^4279*500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202220399 500000000 32566576526911 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5145060719/10000000000 : ℝ)^5303 ≤ (43885785008067/100000000000000 : ℝ)^4279 := by
    have hnat : (5145060719 : ℕ)^5303*100000000000000^4279 ≤ 43885785008067^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145060719 10000000000 43885785008067 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389164517/1250000000 : ℝ)^5303 ≤ (23547638448773/100000000000000 : ℝ)^4279 := by
    have hnat : (389164517 : ℕ)^5303*100000000000000^4279 ≤ 23547638448773^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389164517 1250000000 23547638448773 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(202220399/500000000 : ℝ), (5145060719/10000000000 : ℝ), (389164517/1250000000 : ℝ)] ![(32566576526911/100000000000000 : ℝ), (43885785008067/100000000000000 : ℝ), (23547638448773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(202220399/500000000 : ℝ)|^5303 ≤ (32566576526911/100000000000000 : ℝ)^4279
        have hw : |(202220399/500000000 : ℝ)|=(202220399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5145060719/10000000000 : ℝ)|^5303 ≤ (43885785008067/100000000000000 : ℝ)^4279
        have hw : |(5145060719/10000000000 : ℝ)|=(5145060719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389164517/1250000000 : ℝ)|^5303 ≤ (23547638448773/100000000000000 : ℝ)^4279
        have hw : |(389164517/1250000000 : ℝ)|=(389164517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21909/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5295/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5295 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5295*1^1024 ≤ 0^1024*1^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5295/1024 : ℝ) ≤ (875573544651520769/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5295 ≤ (875573544651520769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5295*100000000000000000000^1024 ≤ 875573544651520769^1024*5^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 875573544651520769 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (875573544651520769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5295 := by
      have hnat : (1 : ℕ)^1024*1^5295 ≤ 1^5295*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100875573544651520769/100000000000000000000 : ℝ) ≤ (10016873235956361/10000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (100875573544651520769/100000000000000000000 : ℝ)^1024 ≤ (10016873235956361/10000000000000000 : ℝ)^5295 := by
      have hnat : (100875573544651520769 : ℕ)^1024*10000000000000000^5295 ≤ 10016873235956361^5295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100875573544651520769 100000000000000000000 10016873235956361 10000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016873235956361/10000000000000000 : ℝ)) (X := (100875573544651520769/100000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50875573544651520769/50000000000000000000 : ℝ) ≤ (5016873235956361/5000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50875573544651520769/50000000000000000000 : ℝ)^1024 ≤ (5016873235956361/5000000000000000 : ℝ)^5295 := by
      have hnat : (50875573544651520769 : ℕ)^1024*5000000000000000^5295 ≤ 5016873235956361^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50875573544651520769 50000000000000000000 5016873235956361 5000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016873235956361/5000000000000000 : ℝ)) (X := (50875573544651520769/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(16873235956361/4000000000000000 : ℝ)*(0 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16873235956361/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(875573544651520769/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(16873235956361/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (1 : ℝ)+(16873235956361/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10016873235956361/10000000000000000 : ℝ) by norm_num, show 1+(875573544651520769/100000000000000000000 : ℝ)+(0 : ℝ)=(100875573544651520769/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(875573544651520769/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(16873235956361/4000000000000000 : ℝ)*(2/5 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16873235956361/4000000000000000 : ℝ)*(2/5 : ℝ)=(5016873235956361/5000000000000000 : ℝ) by norm_num, show 1+2*(875573544651520769/100000000000000000000 : ℝ)=(50875573544651520769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(16873235956361/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16873235956361/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(16873235956361/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16873235956361/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(16873235956361/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16873235956361/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-668295493/5000000000 : ℝ)*X 0 0+(5697849757/10000000000 : ℝ)*X 0 1+(620025649/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2702137507/5000000000 : ℝ)*X 1 0+(-868011631/5000000000 : ℝ)*X 1 1+(49602049/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2702137413/5000000000 : ℝ)*X 2 0+(155006407/312500000 : ℝ)*X 2 1+(-34720467/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4039569441/10000000000 : ℝ)*X 0 0+(3059012633/10000000000 : ℝ)*X 0 1+(5197615233/10000000000 : ℝ)*X 0 2+(4039569441/10000000000 : ℝ)*X 1 0+(3059012633/10000000000 : ℝ)*X 1 1+(5197615233/10000000000 : ℝ)*X 1 2+(4039569441/10000000000 : ℝ)*X 2 0+(3059012633/10000000000 : ℝ)*X 2 1+(5197615233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1338261313/10000000000 : ℝ)*X 0 0+(995666417/2000000000 : ℝ)*X 0 1+(22184057/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5204440731/10000000000 : ℝ)*X 1 0+(-508554603/5000000000 : ℝ)*X 1 1+(2839559331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2602220181/5000000000 : ℝ)*X 2 0+(5679119437/10000000000 : ℝ)*X 2 1+(-508554291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((202220399/500000000 : ℝ)*X 0 0+(5145060719/10000000000 : ℝ)*X 0 1+(389164517/1250000000 : ℝ)*X 0 2+(202220399/500000000 : ℝ)*X 1 0+(5145060719/10000000000 : ℝ)*X 1 1+(389164517/1250000000 : ℝ)*X 1 2+(202220399/500000000 : ℝ)*X 2 0+(5145060719/10000000000 : ℝ)*X 2 1+(389164517/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (165772833653527435823163/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88917523/100000000000000 : ℝ)*(base1) + (153335773/25000000000000 : ℝ)*(base19) + (283091519/50000000000000 : ℝ)*(base23) + (20154851/20000000000000 : ℝ)*(upper3) + (55650279/100000000000000 : ℝ)*(upper5) + (227908349567413/25000000000000 : ℝ)*(major0) + (227908349567413/25000000000000 : ℝ)*(major1) + (227908349567413/25000000000000 : ℝ)*(major2) + (1355668629799853/100000000000000 : ℝ)*(sp0) + (677834830686331/50000000000000 : ℝ)*(sp1) + (338917427133179/25000000000000 : ℝ)*(sp2) + (233797806202741/50000000000000 : ℝ)*(sp3) + (108364589/6250000000000 : ℝ)*(sp4) + (709985321/100000000000000 : ℝ)*(sp7) + (233798205654163/50000000000000 : ℝ)*(f.failure) + (677835137357877/50000000000000 : ℝ)*(f.sum) + (40297377064093/50000000000000000000000000000 : ℝ)*base65 + (43046229064093/100000000000000000000000000000 : ℝ)*base67 + (71421064093/100000000000000000000000000000 : ℝ)*base69 + (406268745335907/100000000000000000000000000000 : ℝ)*base72 + (114126872614093/50000000000000000000000000000 : ℝ)*base73 + (166312619464093/100000000000000000000000000000 : ℝ)*base75 + (34962760135907/100000000000000000000000000000 : ℝ)*base78 + (302180813235907/100000000000000000000000000000 : ℝ)*base80 + (65320277564093/50000000000000000000000000000 : ℝ)*base81 + (859917/500000000000000000000 : ℝ)*base89 + (859917/500000000000000000000 : ℝ)*base91 + (859917/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1469596823380290896636691/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2249011621/100000000000000 : ℝ)*(base19) + (2488712839/100000000000000 : ℝ)*(base23) + (13559337/10000000000000 : ℝ)*(upper2) + (16152127/4000000000000 : ℝ)*(upper3) + (11186593/3125000000000 : ℝ)*(upper5) + (959577344758941/100000000000000 : ℝ)*(major0) + (959577344758941/100000000000000 : ℝ)*(major1) + (959577344758941/100000000000000 : ℝ)*(major2) + (803930673/10000000000000 : ℝ)*(sp1) + (5065832689/50000000000000 : ℝ)*(sp2) + (713483275079923/50000000000000 : ℝ)*(sp4) + (285391252368299/20000000000000 : ℝ)*(sp5) + (1426953929781629/100000000000000 : ℝ)*(sp6) + (19687515777009/4000000000000 : ℝ)*(sp7) + (19687515777009/4000000000000 : ℝ)*(f.failure) + (713483275079923/50000000000000 : ℝ)*(f.sum) + (348236399826299/200000000000000000000000000000 : ℝ)*base66 + (998576866573701/400000000000000000000000000000 : ℝ)*base67 + (1807500167773701/400000000000000000000000000000 : ℝ)*base69 + (1591546114573701/400000000000000000000000000000 : ℝ)*base71 + (74899031573701/200000000000000000000000000000 : ℝ)*base73 + (392099775426299/400000000000000000000000000000 : ℝ)*base76 + (339583370173701/400000000000000000000000000000 : ℝ)*base77 + (1542007652573701/400000000000000000000000000000 : ℝ)*base79 + (658552296173701/200000000000000000000000000000 : ℝ)*base81 + (391569/40000000000000000000 : ℝ)*base90 + (391569/40000000000000000000 : ℝ)*base92 + (391569/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1710_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21909/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1710_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1710_s1_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88027919/625000000 : ℝ)*x 0 + (5484865513/10000000000 : ℝ)*x 1 + (5125888361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88027919/625000000 : ℝ)^5303 ≤ (8811036031907/100000000000000 : ℝ)^4279 := by
    have hnat : (88027919 : ℕ)^5303*100000000000000^4279 ≤ 8811036031907^4279*625000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88027919 625000000 8811036031907 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484865513/10000000000 : ℝ)^5303 ≤ (47505757917999/100000000000000 : ℝ)^4279 := by
    have hnat : (5484865513 : ℕ)^5303*100000000000000^4279 ≤ 47505757917999^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484865513 10000000000 47505757917999 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5125888361/10000000000 : ℝ)^5303 ≤ (43683206032829/100000000000000 : ℝ)^4279 := by
    have hnat : (5125888361 : ℕ)^5303*100000000000000^4279 ≤ 43683206032829^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125888361 10000000000 43683206032829 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88027919/625000000 : ℝ), (5484865513/10000000000 : ℝ), (5125888361/10000000000 : ℝ)] ![(8811036031907/100000000000000 : ℝ), (47505757917999/100000000000000 : ℝ), (43683206032829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88027919/625000000 : ℝ)|^5303 ≤ (8811036031907/100000000000000 : ℝ)^4279
        have hw : |(-88027919/625000000 : ℝ)|=(88027919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484865513/10000000000 : ℝ)|^5303 ≤ (47505757917999/100000000000000 : ℝ)^4279
        have hw : |(5484865513/10000000000 : ℝ)|=(5484865513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5125888361/10000000000 : ℝ)|^5303 ≤ (43683206032829/100000000000000 : ℝ)^4279
        have hw : |(5125888361/10000000000 : ℝ)|=(5125888361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347541581/10000000000 : ℝ)*x 0 + (-1595133369/10000000000 : ℝ)*x 1 + (1281471849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347541581/10000000000 : ℝ)^5303 ≤ (230180868757/500000000000 : ℝ)^4279 := by
    have hnat : (5347541581 : ℕ)^5303*500000000000^4279 ≤ 230180868757^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347541581 10000000000 230180868757 500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1595133369/10000000000 : ℝ)^5303 ≤ (2056126078773/20000000000000 : ℝ)^4279 := by
    have hnat : (1595133369 : ℕ)^5303*20000000000000^4279 ≤ 2056126078773^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595133369 10000000000 2056126078773 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281471849/2500000000 : ℝ)^5303 ≤ (43683195841003/100000000000000 : ℝ)^4279 := by
    have hnat : (1281471849 : ℕ)^5303*100000000000000^4279 ≤ 43683195841003^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281471849 2500000000 43683195841003 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347541581/10000000000 : ℝ), (-1595133369/10000000000 : ℝ), (1281471849/2500000000 : ℝ)] ![(230180868757/500000000000 : ℝ), (2056126078773/20000000000000 : ℝ), (43683195841003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347541581/10000000000 : ℝ)|^5303 ≤ (230180868757/500000000000 : ℝ)^4279
        have hw : |(5347541581/10000000000 : ℝ)|=(5347541581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1595133369/10000000000 : ℝ)|^5303 ≤ (2056126078773/20000000000000 : ℝ)^4279
        have hw : |(-1595133369/10000000000 : ℝ)|=(1595133369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281471849/2500000000 : ℝ)|^5303 ≤ (43683195841003/100000000000000 : ℝ)^4279
        have hw : |(1281471849/2500000000 : ℝ)|=(1281471849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347540191/10000000000 : ℝ)*x 0 + (2562944297/5000000000 : ℝ)*x 1 + (-797566821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347540191/10000000000 : ℝ)^5303 ≤ (46036158921467/100000000000000 : ℝ)^4279 := by
    have hnat : (5347540191 : ℕ)^5303*100000000000000^4279 ≤ 46036158921467^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347540191 10000000000 46036158921467 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562944297/5000000000 : ℝ)^5303 ≤ (43683208493653/100000000000000 : ℝ)^4279 := by
    have hnat : (2562944297 : ℕ)^5303*100000000000000^4279 ≤ 43683208493653^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562944297 5000000000 43683208493653 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797566821/5000000000 : ℝ)^5303 ≤ (1285079071801/12500000000000 : ℝ)^4279 := by
    have hnat : (797566821 : ℕ)^5303*12500000000000^4279 ≤ 1285079071801^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797566821 5000000000 1285079071801 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347540191/10000000000 : ℝ), (2562944297/5000000000 : ℝ), (-797566821/5000000000 : ℝ)] ![(46036158921467/100000000000000 : ℝ), (43683208493653/100000000000000 : ℝ), (1285079071801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347540191/10000000000 : ℝ)|^5303 ≤ (46036158921467/100000000000000 : ℝ)^4279
        have hw : |(5347540191/10000000000 : ℝ)|=(5347540191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562944297/5000000000 : ℝ)|^5303 ≤ (43683208493653/100000000000000 : ℝ)^4279
        have hw : |(2562944297/5000000000 : ℝ)|=(2562944297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-797566821/5000000000 : ℝ)|^5303 ≤ (1285079071801/12500000000000 : ℝ)^4279
        have hw : |(-797566821/5000000000 : ℝ)|=(797566821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025476479/2500000000 : ℝ)*x 0 + (3602394799/10000000000 : ℝ)*x 1 + (928630267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025476479/2500000000 : ℝ)^5303 ≤ (33141333493949/100000000000000 : ℝ)^4279 := by
    have hnat : (1025476479 : ℕ)^5303*100000000000000^4279 ≤ 33141333493949^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025476479 2500000000 33141333493949 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3602394799/10000000000 : ℝ)^5303 ≤ (28214993122631/100000000000000 : ℝ)^4279 := by
    have hnat : (3602394799 : ℕ)^5303*100000000000000^4279 ≤ 28214993122631^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3602394799 10000000000 28214993122631 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928630267/2000000000 : ℝ)^5303 ≤ (38643673368599/100000000000000 : ℝ)^4279 := by
    have hnat : (928630267 : ℕ)^5303*100000000000000^4279 ≤ 38643673368599^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928630267 2000000000 38643673368599 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025476479/2500000000 : ℝ), (3602394799/10000000000 : ℝ), (928630267/2000000000 : ℝ)] ![(33141333493949/100000000000000 : ℝ), (28214993122631/100000000000000 : ℝ), (38643673368599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025476479/2500000000 : ℝ)|^5303 ≤ (33141333493949/100000000000000 : ℝ)^4279
        have hw : |(1025476479/2500000000 : ℝ)|=(1025476479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3602394799/10000000000 : ℝ)|^5303 ≤ (28214993122631/100000000000000 : ℝ)^4279
        have hw : |(3602394799/10000000000 : ℝ)|=(3602394799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928630267/2000000000 : ℝ)|^5303 ≤ (38643673368599/100000000000000 : ℝ)^4279
        have hw : |(928630267/2000000000 : ℝ)|=(928630267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-281727669/2000000000 : ℝ)*x 0 + (5130186831/10000000000 : ℝ)*x 1 + (5480496849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281727669/2000000000 : ℝ)^5303 ≤ (8812521835481/100000000000000 : ℝ)^4279 := by
    have hnat : (281727669 : ℕ)^5303*100000000000000^4279 ≤ 8812521835481^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281727669 2000000000 8812521835481 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130186831/10000000000 : ℝ)^5303 ≤ (21864304391907/50000000000000 : ℝ)^4279 := by
    have hnat : (5130186831 : ℕ)^5303*50000000000000^4279 ≤ 21864304391907^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130186831 10000000000 21864304391907 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480496849/10000000000 : ℝ)^5303 ≤ (47458869362649/100000000000000 : ℝ)^4279 := by
    have hnat : (5480496849 : ℕ)^5303*100000000000000^4279 ≤ 47458869362649^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480496849 10000000000 47458869362649 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-281727669/2000000000 : ℝ), (5130186831/10000000000 : ℝ), (5480496849/10000000000 : ℝ)] ![(8812521835481/100000000000000 : ℝ), (21864304391907/50000000000000 : ℝ), (47458869362649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-281727669/2000000000 : ℝ)|^5303 ≤ (8812521835481/100000000000000 : ℝ)^4279
        have hw : |(-281727669/2000000000 : ℝ)|=(281727669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130186831/10000000000 : ℝ)|^5303 ≤ (21864304391907/50000000000000 : ℝ)^4279
        have hw : |(5130186831/10000000000 : ℝ)|=(5130186831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480496849/10000000000 : ℝ)|^5303 ≤ (47458869362649/100000000000000 : ℝ)^4279
        have hw : |(5480496849/10000000000 : ℝ)|=(5480496849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_5 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312853963/2500000000 : ℝ)*x 0 + (-1240524289/10000000000 : ℝ)*x 1 + (685062073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312853963/2500000000 : ℝ)^5303 ≤ (22506411371773/50000000000000 : ℝ)^4279 := by
    have hnat : (1312853963 : ℕ)^5303*50000000000000^4279 ≤ 22506411371773^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312853963 2500000000 22506411371773 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1240524289/10000000000 : ℝ)^5303 ≤ (3764155364887/50000000000000 : ℝ)^4279 := by
    have hnat : (1240524289 : ℕ)^5303*50000000000000^4279 ≤ 3764155364887^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240524289 10000000000 3764155364887 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685062073/1250000000 : ℝ)^5303 ≤ (23729433259347/50000000000000 : ℝ)^4279 := by
    have hnat : (685062073 : ℕ)^5303*50000000000000^4279 ≤ 23729433259347^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685062073 1250000000 23729433259347 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312853963/2500000000 : ℝ), (-1240524289/10000000000 : ℝ), (685062073/1250000000 : ℝ)] ![(22506411371773/50000000000000 : ℝ), (3764155364887/50000000000000 : ℝ), (23729433259347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312853963/2500000000 : ℝ)|^5303 ≤ (22506411371773/50000000000000 : ℝ)^4279
        have hw : |(1312853963/2500000000 : ℝ)|=(1312853963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1240524289/10000000000 : ℝ)|^5303 ≤ (3764155364887/50000000000000 : ℝ)^4279
        have hw : |(-1240524289/10000000000 : ℝ)|=(1240524289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685062073/1250000000 : ℝ)|^5303 ≤ (23729433259347/50000000000000 : ℝ)^4279
        have hw : |(685062073/1250000000 : ℝ)|=(685062073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_6 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251415943/10000000000 : ℝ)*x 0 + (685062037/1250000000 : ℝ)*x 1 + (-124052457/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251415943/10000000000 : ℝ)^5303 ≤ (45012823710221/100000000000000 : ℝ)^4279 := by
    have hnat : (5251415943 : ℕ)^5303*100000000000000^4279 ≤ 45012823710221^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251415943 10000000000 45012823710221 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685062037/1250000000 : ℝ)^5303 ≤ (23729431713953/50000000000000 : ℝ)^4279 := by
    have hnat : (685062037 : ℕ)^5303*50000000000000^4279 ≤ 23729431713953^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685062037 1250000000 23729431713953 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124052457/1000000000 : ℝ)^5303 ≤ (1882078210789/25000000000000 : ℝ)^4279 := by
    have hnat : (124052457 : ℕ)^5303*25000000000000^4279 ≤ 1882078210789^4279*1000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124052457 1000000000 1882078210789 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251415943/10000000000 : ℝ), (685062037/1250000000 : ℝ), (-124052457/1000000000 : ℝ)] ![(45012823710221/100000000000000 : ℝ), (23729431713953/50000000000000 : ℝ), (1882078210789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251415943/10000000000 : ℝ)|^5303 ≤ (45012823710221/100000000000000 : ℝ)^4279
        have hw : |(5251415943/10000000000 : ℝ)|=(5251415943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685062037/1250000000 : ℝ)|^5303 ≤ (23729431713953/50000000000000 : ℝ)^4279
        have hw : |(685062037/1250000000 : ℝ)|=(685062037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124052457/1000000000 : ℝ)|^5303 ≤ (1882078210789/25000000000000 : ℝ)^4279
        have hw : |(-124052457/1000000000 : ℝ)|=(124052457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s1_7 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102459047/10000000000 : ℝ)*x 0 + (4630687921/10000000000 : ℝ)*x 1 + (3615058463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102459047/10000000000 : ℝ)^5303 ≤ (3314687207647/10000000000000 : ℝ)^4279 := by
    have hnat : (4102459047 : ℕ)^5303*10000000000000^4279 ≤ 3314687207647^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102459047 10000000000 3314687207647 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4630687921/10000000000 : ℝ)^5303 ≤ (770303235433/2000000000000 : ℝ)^4279 := by
    have hnat : (4630687921 : ℕ)^5303*2000000000000^4279 ≤ 770303235433^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4630687921 10000000000 770303235433 2000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3615058463/10000000000 : ℝ)^5303 ≤ (3542245767733/12500000000000 : ℝ)^4279 := by
    have hnat : (3615058463 : ℕ)^5303*12500000000000^4279 ≤ 3542245767733^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615058463 10000000000 3542245767733 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102459047/10000000000 : ℝ), (4630687921/10000000000 : ℝ), (3615058463/10000000000 : ℝ)] ![(3314687207647/10000000000000 : ℝ), (770303235433/2000000000000 : ℝ), (3542245767733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102459047/10000000000 : ℝ)|^5303 ≤ (3314687207647/10000000000000 : ℝ)^4279
        have hw : |(4102459047/10000000000 : ℝ)|=(4102459047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4630687921/10000000000 : ℝ)|^5303 ≤ (770303235433/2000000000000 : ℝ)^4279
        have hw : |(4630687921/10000000000 : ℝ)|=(4630687921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3615058463/10000000000 : ℝ)|^5303 ≤ (3542245767733/12500000000000 : ℝ)^4279
        have hw : |(3615058463/10000000000 : ℝ)|=(3615058463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (487/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3481/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21909/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21909/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21909/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6051/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (50228698893407/100000000000000000000 : ℝ) := by
    have hpowers : (6051/100000 : ℝ)^5295 ≤ (50228698893407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6051 : ℕ)^5295*100000000000000000000^1024 ≤ 50228698893407^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6051 100000 50228698893407 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6051/100000 : ℝ)) (X := (50228698893407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21909/100000 : ℝ) ^ (5295/1024 : ℝ) ≤ (38942712803409301/100000000000000000000 : ℝ) := by
    have hpowers : (21909/100000 : ℝ)^5295 ≤ (38942712803409301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (21909 : ℕ)^5295*100000000000000000000^1024 ≤ 38942712803409301^1024*100000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21909 100000 38942712803409301 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21909/100000 : ℝ)) (X := (38942712803409301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000050228698893407/50000000000000000000 : ℝ) ≤ (5000000971372367/5000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50000050228698893407/50000000000000000000 : ℝ)^1024 ≤ (5000000971372367/5000000000000000 : ℝ)^5295 := by
      have hnat : (50000050228698893407 : ℕ)^1024*5000000000000000^5295 ≤ 5000000971372367^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000050228698893407 50000000000000000000 5000000971372367 5000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000971372367/5000000000000000 : ℝ)) (X := (50000050228698893407/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009748235375575677/25000000000000000000 : ℝ) ≤ (2500188491474761/2500000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (25009748235375575677/25000000000000000000 : ℝ)^1024 ≤ (2500188491474761/2500000000000000 : ℝ)^5295 := by
      have hnat : (25009748235375575677 : ℕ)^1024*2500000000000000^5295 ≤ 2500188491474761^5295*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009748235375575677 25000000000000000000 2500188491474761 2500000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500188491474761/2500000000000000 : ℝ)) (X := (25009748235375575677/25000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038942712803409301/50000000000000000000 : ℝ) ≤ (5000752994526677/5000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50038942712803409301/50000000000000000000 : ℝ)^1024 ≤ (5000752994526677/5000000000000000 : ℝ)^5295 := by
      have hnat : (50038942712803409301 : ℕ)^1024*5000000000000000^5295 ≤ 5000752994526677^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038942712803409301 50000000000000000000 5000752994526677 5000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000752994526677/5000000000000000 : ℝ)) (X := (50038942712803409301/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50228698893407/100000000000000000000 : ℝ) ≤ ((2202374025331007391/2202500000000000000 : ℝ)+2*(25067438477/52860000000000 : ℝ)*(6051/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (2202374025331007391/2202500000000000000 : ℝ)+2*(25067438477/52860000000000 : ℝ)*(6051/100000 : ℝ)=(5000000971372367/5000000000000000 : ℝ) by norm_num, show 1+2*(50228698893407/100000000000000000000 : ℝ)=(50000050228698893407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38942712803409301/100000000000000000000 : ℝ)+(50228698893407/100000000000000000000 : ℝ) ≤ ((2202374025331007391/2202500000000000000 : ℝ)+(25067438477/52860000000000 : ℝ)*((21909/100000 : ℝ)+(6051/100000 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (2202374025331007391/2202500000000000000 : ℝ)+(25067438477/52860000000000 : ℝ)*((21909/100000 : ℝ)+(6051/100000 : ℝ))=(2500188491474761/2500000000000000 : ℝ) by norm_num, show 1+(38942712803409301/100000000000000000000 : ℝ)+(50228698893407/100000000000000000000 : ℝ)=(25009748235375575677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38942712803409301/100000000000000000000 : ℝ) ≤ ((2202374025331007391/2202500000000000000 : ℝ)+2*(25067438477/52860000000000 : ℝ)*(21909/100000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (2202374025331007391/2202500000000000000 : ℝ)+2*(25067438477/52860000000000 : ℝ)*(21909/100000 : ℝ)=(5000752994526677/5000000000000000 : ℝ) by norm_num, show 1+2*(38942712803409301/100000000000000000000 : ℝ)=(50038942712803409301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2202374025331007391/2202500000000000000 : ℝ)*(X 1 0+X 2 0)+(25067438477/52860000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (6051/100000 : ℝ)) (hi := (21909/100000 : ℝ)) (c := (2202374025331007391/2202500000000000000 : ℝ)) (alpha := (25067438477/52860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2202374025331007391/2202500000000000000 : ℝ)*(X 0 1+X 2 1)+(25067438477/52860000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (6051/100000 : ℝ)) (hi := (21909/100000 : ℝ)) (c := (2202374025331007391/2202500000000000000 : ℝ)) (alpha := (25067438477/52860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2202374025331007391/2202500000000000000 : ℝ)*(X 0 2+X 1 2)+(25067438477/52860000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (6051/100000 : ℝ)) (hi := (21909/100000 : ℝ)) (c := (2202374025331007391/2202500000000000000 : ℝ)) (alpha := (25067438477/52860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88027919/625000000 : ℝ)*X 0 0+(5484865513/10000000000 : ℝ)*X 0 1+(5125888361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347541581/10000000000 : ℝ)*X 1 0+(-1595133369/10000000000 : ℝ)*X 1 1+(1281471849/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347540191/10000000000 : ℝ)*X 2 0+(2562944297/5000000000 : ℝ)*X 2 1+(-797566821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1025476479/2500000000 : ℝ)*X 0 0+(3602394799/10000000000 : ℝ)*X 0 1+(928630267/2000000000 : ℝ)*X 0 2+(1025476479/2500000000 : ℝ)*X 1 0+(3602394799/10000000000 : ℝ)*X 1 1+(928630267/2000000000 : ℝ)*X 1 2+(1025476479/2500000000 : ℝ)*X 2 0+(3602394799/10000000000 : ℝ)*X 2 1+(928630267/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-281727669/2000000000 : ℝ)*X 0 0+(5130186831/10000000000 : ℝ)*X 0 1+(5480496849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1312853963/2500000000 : ℝ)*X 1 0+(-1240524289/10000000000 : ℝ)*X 1 1+(685062073/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251415943/10000000000 : ℝ)*X 2 0+(685062037/1250000000 : ℝ)*X 2 1+(-124052457/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4102459047/10000000000 : ℝ)*X 0 0+(4630687921/10000000000 : ℝ)*X 0 1+(3615058463/10000000000 : ℝ)*X 0 2+(4102459047/10000000000 : ℝ)*X 1 0+(4630687921/10000000000 : ℝ)*X 1 1+(3615058463/10000000000 : ℝ)*X 1 2+(4102459047/10000000000 : ℝ)*X 2 0+(4630687921/10000000000 : ℝ)*X 2 1+(3615058463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151973211825707034860923787/13765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57891083/5000000000000 : ℝ)*(base19) + (525122249/100000000000000 : ℝ)*(base23) + (67852473/100000000000000 : ℝ)*(lower2) + (3959191/2000000000000 : ℝ)*(upper3) + (116726653/100000000000000 : ℝ)*(lower4) + (234159185305303/12500000000000 : ℝ)*(major0) + (234159185305303/12500000000000 : ℝ)*(major1) + (234159185305303/12500000000000 : ℝ)*(major2) + (278570151659133/10000000000000 : ℝ)*(sp0) + (278570310984039/10000000000000 : ℝ)*(sp1) + (2785703742539801/100000000000000 : ℝ)*(sp2) + (480420400147847/50000000000000 : ℝ)*(sp3) + (2751070719/100000000000000 : ℝ)*(sp4) + (1528925371/100000000000000 : ℝ)*(sp7) + (192168465844213/20000000000000 : ℝ)*(f.failure) + (55714085353241/2000000000000 : ℝ)*(f.sum) + (471713100629/264300000000000000000000000 : ℝ)*base66 + (960132462545858419/82593750000000000000000000000000 : ℝ)*base67 + (175008841850108419/82593750000000000000000000000000 : ℝ)*base69 + (598989576437577169/82593750000000000000000000000000 : ℝ)*base71 + (2144745794707/2643000000000000000000000000 : ℝ)*base73 + (236023074718547831/82593750000000000000000000000000 : ℝ)*base76 + (64906557223733419/82593750000000000000000000000000 : ℝ)*base77 + (6866288869452169/82593750000000000000000000000000 : ℝ)*base79 + (1498255468051/528600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2122133/200000000000000000000 : ℝ)*base90 + (2122133/200000000000000000000 : ℝ)*base92 + (2122133/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75861088422239484526583779/6882812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (216289227/10000000000000 : ℝ)*(base19) + (2285174429/100000000000000 : ℝ)*(base23) + (56498839/100000000000000 : ℝ)*(upper2) + (148049547/50000000000000 : ℝ)*(upper3) + (20934469/6250000000000 : ℝ)*(upper5) + (479903170440629/25000000000000 : ℝ)*(major0) + (479903170440629/25000000000000 : ℝ)*(major1) + (479903170440629/25000000000000 : ℝ)*(major2) + (1708284919/10000000000000 : ℝ)*(sp1) + (7591725009/50000000000000 : ℝ)*(sp2) + (570922858638183/20000000000000 : ℝ)*(sp4) + (1427297523724727/50000000000000 : ℝ)*(sp5) + (713649206141617/25000000000000 : ℝ)*(sp6) + (123076337867533/12500000000000 : ℝ)*(sp7) + (123076337867533/12500000000000 : ℝ)*(f.failure) + (570922858638183/20000000000000 : ℝ)*(f.sum) + (7001077885187/2643000000000000000000000000 : ℝ)*base66 + (1269275424388254317/165187500000000000000000000000000 : ℝ)*base67 + (163641819473870683/165187500000000000000000000000000 : ℝ)*base70 + (848478257552566817/165187500000000000000000000000000 : ℝ)*base71 + (1217391434591/330375000000000000000000000 : ℝ)*base73 + (1564789733597191817/165187500000000000000000000000000 : ℝ)*base75 + (347702677261816817/165187500000000000000000000000000 : ℝ)*base77 + (1366198057652941817/165187500000000000000000000000000 : ℝ)*base79 + (700958371241/165187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (694253/125000000000000000000 : ℝ)*base90 + (694253/125000000000000000000 : ℝ)*base92 + (694253/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1710_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21909/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (487/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3481/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1710_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1710_s2_0 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1411937527/10000000000 : ℝ)*x 0 + (5470560071/10000000000 : ℝ)*x 1 + (1027571249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1411937527/10000000000 : ℝ)^5303 ≤ (883810816173/10000000000000 : ℝ)^4279 := by
    have hnat : (1411937527 : ℕ)^5303*10000000000000^4279 ≤ 883810816173^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411937527 10000000000 883810816173 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470560071/10000000000 : ℝ)^5303 ≤ (23676125978479/50000000000000 : ℝ)^4279 := by
    have hnat : (5470560071 : ℕ)^5303*50000000000000^4279 ≤ 23676125978479^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470560071 10000000000 23676125978479 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027571249/2000000000 : ℝ)^5303 ≤ (8761927973643/20000000000000 : ℝ)^4279 := by
    have hnat : (1027571249 : ℕ)^5303*20000000000000^4279 ≤ 8761927973643^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027571249 2000000000 8761927973643 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1411937527/10000000000 : ℝ), (5470560071/10000000000 : ℝ), (1027571249/2000000000 : ℝ)] ![(883810816173/10000000000000 : ℝ), (23676125978479/50000000000000 : ℝ), (8761927973643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1411937527/10000000000 : ℝ)|^5303 ≤ (883810816173/10000000000000 : ℝ)^4279
        have hw : |(-1411937527/10000000000 : ℝ)|=(1411937527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470560071/10000000000 : ℝ)|^5303 ≤ (23676125978479/50000000000000 : ℝ)^4279
        have hw : |(5470560071/10000000000 : ℝ)|=(5470560071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027571249/2000000000 : ℝ)|^5303 ≤ (8761927973643/20000000000000 : ℝ)^4279
        have hw : |(1027571249/2000000000 : ℝ)|=(1027571249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_1 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343664943/10000000000 : ℝ)*x 0 + (-1584472019/10000000000 : ℝ)*x 1 + (1027571247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343664943/10000000000 : ℝ)^5303 ≤ (359334511129/781250000000 : ℝ)^4279 := by
    have hnat : (5343664943 : ℕ)^5303*781250000000^4279 ≤ 359334511129^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343664943 10000000000 359334511129 781250000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1584472019/10000000000 : ℝ)^5303 ≤ (1274442850079/12500000000000 : ℝ)^4279 := by
    have hnat : (1584472019 : ℕ)^5303*12500000000000^4279 ≤ 1274442850079^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584472019 10000000000 1274442850079 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027571247/2000000000 : ℝ)^5303 ≤ (21904819881271/50000000000000 : ℝ)^4279 := by
    have hnat : (1027571247 : ℕ)^5303*50000000000000^4279 ≤ 21904819881271^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027571247 2000000000 21904819881271 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343664943/10000000000 : ℝ), (-1584472019/10000000000 : ℝ), (1027571247/2000000000 : ℝ)] ![(359334511129/781250000000 : ℝ), (1274442850079/12500000000000 : ℝ), (21904819881271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343664943/10000000000 : ℝ)|^5303 ≤ (359334511129/781250000000 : ℝ)^4279
        have hw : |(5343664943/10000000000 : ℝ)|=(5343664943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1584472019/10000000000 : ℝ)|^5303 ≤ (1274442850079/12500000000000 : ℝ)^4279
        have hw : |(-1584472019/10000000000 : ℝ)|=(1584472019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027571247/2000000000 : ℝ)|^5303 ≤ (21904819881271/50000000000000 : ℝ)^4279
        have hw : |(1027571247/2000000000 : ℝ)|=(1027571247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_2 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213746603/400000000 : ℝ)*x 0 + (1284464091/2500000000 : ℝ)*x 1 + (-198058959/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213746603/400000000 : ℝ)^5303 ≤ (22997409416289/50000000000000 : ℝ)^4279 := by
    have hnat : (213746603 : ℕ)^5303*50000000000000^4279 ≤ 22997409416289^4279*400000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213746603 400000000 22997409416289 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284464091/2500000000 : ℝ)^5303 ≤ (43809641125733/100000000000000 : ℝ)^4279 := by
    have hnat : (1284464091 : ℕ)^5303*100000000000000^4279 ≤ 43809641125733^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284464091 2500000000 43809641125733 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198058959/1250000000 : ℝ)^5303 ≤ (1019554003347/10000000000000 : ℝ)^4279 := by
    have hnat : (198058959 : ℕ)^5303*10000000000000^4279 ≤ 1019554003347^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198058959 1250000000 1019554003347 10000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213746603/400000000 : ℝ), (1284464091/2500000000 : ℝ), (-198058959/1250000000 : ℝ)] ![(22997409416289/50000000000000 : ℝ), (43809641125733/100000000000000 : ℝ), (1019554003347/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213746603/400000000 : ℝ)|^5303 ≤ (22997409416289/50000000000000 : ℝ)^4279
        have hw : |(213746603/400000000 : ℝ)|=(213746603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284464091/2500000000 : ℝ)|^5303 ≤ (43809641125733/100000000000000 : ℝ)^4279
        have hw : |(1284464091/2500000000 : ℝ)|=(1284464091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198058959/1250000000 : ℝ)|^5303 ≤ (1019554003347/10000000000000 : ℝ)^4279
        have hw : |(-198058959/1250000000 : ℝ)|=(198058959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_3 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026152601/2500000000 : ℝ)*x 0 + (728048487/2000000000 : ℝ)*x 1 + (4604825721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026152601/2500000000 : ℝ)^5303 ≤ (33168415631423/100000000000000 : ℝ)^4279 := by
    have hnat : (1026152601 : ℕ)^5303*100000000000000^4279 ≤ 33168415631423^4279*2500000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026152601 2500000000 33168415631423 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (728048487/2000000000 : ℝ)^5303 ≤ (14291413154863/50000000000000 : ℝ)^4279 := by
    have hnat : (728048487 : ℕ)^5303*50000000000000^4279 ≤ 14291413154863^4279*2000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728048487 2000000000 14291413154863 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4604825721/10000000000 : ℝ)^5303 ≤ (38248758050249/100000000000000 : ℝ)^4279 := by
    have hnat : (4604825721 : ℕ)^5303*100000000000000^4279 ≤ 38248758050249^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604825721 10000000000 38248758050249 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026152601/2500000000 : ℝ), (728048487/2000000000 : ℝ), (4604825721/10000000000 : ℝ)] ![(33168415631423/100000000000000 : ℝ), (14291413154863/50000000000000 : ℝ), (38248758050249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026152601/2500000000 : ℝ)|^5303 ≤ (33168415631423/100000000000000 : ℝ)^4279
        have hw : |(1026152601/2500000000 : ℝ)|=(1026152601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(728048487/2000000000 : ℝ)|^5303 ≤ (14291413154863/50000000000000 : ℝ)^4279
        have hw : |(728048487/2000000000 : ℝ)|=(728048487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4604825721/10000000000 : ℝ)|^5303 ≤ (38248758050249/100000000000000 : ℝ)^4279
        have hw : |(4604825721/10000000000 : ℝ)|=(4604825721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_4 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-176511227/1250000000 : ℝ)*x 0 + (5141551491/10000000000 : ℝ)*x 1 + (683351143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176511227/1250000000 : ℝ)^5303 ≤ (2209822390667/25000000000000 : ℝ)^4279 := by
    have hnat : (176511227 : ℕ)^5303*25000000000000^4279 ≤ 2209822390667^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176511227 1250000000 2209822390667 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141551491/10000000000 : ℝ)^5303 ≤ (21924346137143/50000000000000 : ℝ)^4279 := by
    have hnat : (5141551491 : ℕ)^5303*50000000000000^4279 ≤ 21924346137143^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141551491 10000000000 21924346137143 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683351143/1250000000 : ℝ)^5303 ≤ (47312018146899/100000000000000 : ℝ)^4279 := by
    have hnat : (683351143 : ℕ)^5303*100000000000000^4279 ≤ 47312018146899^4279*1250000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683351143 1250000000 47312018146899 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176511227/1250000000 : ℝ), (5141551491/10000000000 : ℝ), (683351143/1250000000 : ℝ)] ![(2209822390667/25000000000000 : ℝ), (21924346137143/50000000000000 : ℝ), (47312018146899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176511227/1250000000 : ℝ)|^5303 ≤ (2209822390667/25000000000000 : ℝ)^4279
        have hw : |(-176511227/1250000000 : ℝ)|=(176511227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141551491/10000000000 : ℝ)|^5303 ≤ (21924346137143/50000000000000 : ℝ)^4279
        have hw : |(5141551491/10000000000 : ℝ)|=(5141551491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683351143/1250000000 : ℝ)|^5303 ≤ (47312018146899/100000000000000 : ℝ)^4279
        have hw : |(683351143/1250000000 : ℝ)|=(683351143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_5 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254608043/10000000000 : ℝ)*x 0 + (-627759469/5000000000 : ℝ)*x 1 + (5466809103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254608043/10000000000 : ℝ)^5303 ≤ (45046735229673/100000000000000 : ℝ)^4279 := by
    have hnat : (5254608043 : ℕ)^5303*100000000000000^4279 ≤ 45046735229673^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254608043 10000000000 45046735229673 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627759469/5000000000 : ℝ)^5303 ≤ (477577941119/6250000000000 : ℝ)^4279 := by
    have hnat : (627759469 : ℕ)^5303*6250000000000^4279 ≤ 477577941119^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627759469 5000000000 477577941119 6250000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466809103/10000000000 : ℝ)^5303 ≤ (9462403541431/20000000000000 : ℝ)^4279 := by
    have hnat : (5466809103 : ℕ)^5303*20000000000000^4279 ≤ 9462403541431^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466809103 10000000000 9462403541431 20000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254608043/10000000000 : ℝ), (-627759469/5000000000 : ℝ), (5466809103/10000000000 : ℝ)] ![(45046735229673/100000000000000 : ℝ), (477577941119/6250000000000 : ℝ), (9462403541431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254608043/10000000000 : ℝ)|^5303 ≤ (45046735229673/100000000000000 : ℝ)^4279
        have hw : |(5254608043/10000000000 : ℝ)|=(5254608043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627759469/5000000000 : ℝ)|^5303 ≤ (477577941119/6250000000000 : ℝ)^4279
        have hw : |(-627759469/5000000000 : ℝ)|=(627759469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466809103/10000000000 : ℝ)|^5303 ≤ (9462403541431/20000000000000 : ℝ)^4279
        have hw : |(5466809103/10000000000 : ℝ)|=(5466809103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_6 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328412999/625000000 : ℝ)*x 0 + (5466809107/10000000000 : ℝ)*x 1 + (-1255519013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328412999/625000000 : ℝ)^5303 ≤ (11261683650709/25000000000000 : ℝ)^4279 := by
    have hnat : (328412999 : ℕ)^5303*25000000000000^4279 ≤ 11261683650709^4279*625000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328412999 625000000 11261683650709 25000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466809107/10000000000 : ℝ)^5303 ≤ (47312017750057/100000000000000 : ℝ)^4279 := by
    have hnat : (5466809107 : ℕ)^5303*100000000000000^4279 ≤ 47312017750057^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466809107 10000000000 47312017750057 100000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255519013/10000000000 : ℝ)^5303 ≤ (3820623811799/50000000000000 : ℝ)^4279 := by
    have hnat : (1255519013 : ℕ)^5303*50000000000000^4279 ≤ 3820623811799^4279*10000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255519013 10000000000 3820623811799 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328412999/625000000 : ℝ), (5466809107/10000000000 : ℝ), (-1255519013/10000000000 : ℝ)] ![(11261683650709/25000000000000 : ℝ), (47312017750057/100000000000000 : ℝ), (3820623811799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328412999/625000000 : ℝ)|^5303 ≤ (11261683650709/25000000000000 : ℝ)^4279
        have hw : |(328412999/625000000 : ℝ)|=(328412999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466809107/10000000000 : ℝ)|^5303 ≤ (47312017750057/100000000000000 : ℝ)^4279
        have hw : |(5466809107/10000000000 : ℝ)|=(5466809107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1255519013/10000000000 : ℝ)|^5303 ≤ (3820623811799/50000000000000 : ℝ)^4279
        have hw : |(-1255519013/10000000000 : ℝ)|=(1255519013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1710_s2_7 (p : ℝ) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2052525371/5000000000 : ℝ)*x 0 + (287132023/625000000 : ℝ)*x 1 + (228194717/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052525371/5000000000 : ℝ)^5303 ≤ (16586412740959/50000000000000 : ℝ)^4279 := by
    have hnat : (2052525371 : ℕ)^5303*50000000000000^4279 ≤ 16586412740959^4279*5000000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052525371 5000000000 16586412740959 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287132023/625000000 : ℝ)^5303 ≤ (4767313210857/12500000000000 : ℝ)^4279 := by
    have hnat : (287132023 : ℕ)^5303*12500000000000^4279 ≤ 4767313210857^4279*625000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287132023 625000000 4767313210857 12500000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228194717/625000000 : ℝ)^5303 ≤ (14344334410823/50000000000000 : ℝ)^4279 := by
    have hnat : (228194717 : ℕ)^5303*50000000000000^4279 ≤ 14344334410823^4279*625000000^5303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228194717 625000000 14344334410823 50000000000000 5303 4279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5303/1024 : ℝ)) 5303 4279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052525371/5000000000 : ℝ), (287132023/625000000 : ℝ), (228194717/625000000 : ℝ)] ![(16586412740959/50000000000000 : ℝ), (4767313210857/12500000000000 : ℝ), (14344334410823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052525371/5000000000 : ℝ)|^5303 ≤ (16586412740959/50000000000000 : ℝ)^4279
        have hw : |(2052525371/5000000000 : ℝ)|=(2052525371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287132023/625000000 : ℝ)|^5303 ≤ (4767313210857/12500000000000 : ℝ)^4279
        have hw : |(287132023/625000000 : ℝ)|=(287132023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228194717/625000000 : ℝ)|^5303 ≤ (14344334410823/50000000000000 : ℝ)^4279
        have hw : |(228194717/625000000 : ℝ)|=(228194717/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1710_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3481/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (487/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1069/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3481/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (487/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3481/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (487/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3481/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (487/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3481/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (487/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3481/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (487/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3481/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (487/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (487/5000 : ℝ) ^ (5295/1024 : ℝ) ≤ (588763787583681/100000000000000000000 : ℝ) := by
    have hpowers : (487/5000 : ℝ)^5295 ≤ (588763787583681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (487 : ℕ)^5295*100000000000000000000^1024 ≤ 588763787583681^1024*5000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        487 5000 588763787583681 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (487/5000 : ℝ)) (X := (588763787583681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3481/20000 : ℝ) ^ (5295/1024 : ℝ) ≤ (11846839804379367/100000000000000000000 : ℝ) := by
    have hpowers : (3481/20000 : ℝ)^5295 ≤ (11846839804379367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3481 : ℕ)^5295*100000000000000000000^1024 ≤ 11846839804379367^1024*20000^5295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3481 20000 11846839804379367 100000000000000000000 5295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3481/20000 : ℝ)) (X := (11846839804379367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000588763787583681/50000000000000000000 : ℝ) ≤ (250000569302413/250000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50000588763787583681/50000000000000000000 : ℝ)^1024 ≤ (250000569302413/250000000000000 : ℝ)^5295 := by
      have hnat : (50000588763787583681 : ℕ)^1024*250000000000000^5295 ≤ 250000569302413^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000588763787583681 50000000000000000000 250000569302413 250000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000569302413/250000000000000 : ℝ)) (X := (50000588763787583681/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501554450448995381/12500000000000000000 : ℝ) ≤ (400009619202621/400000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (12501554450448995381/12500000000000000000 : ℝ)^1024 ≤ (400009619202621/400000000000000 : ℝ)^5295 := by
      have hnat : (12501554450448995381 : ℕ)^1024*400000000000000^5295 ≤ 400009619202621^5295*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501554450448995381 12500000000000000000 400009619202621 400000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400009619202621/400000000000000 : ℝ)) (X := (12501554450448995381/12500000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011846839804379367/50000000000000000000 : ℝ) ≤ (1000045818803453/1000000000000000 : ℝ) ^ (5295/1024 : ℝ) := by
    have hpowers : (50011846839804379367/50000000000000000000 : ℝ)^1024 ≤ (1000045818803453/1000000000000000 : ℝ)^5295 := by
      have hnat : (50011846839804379367 : ℕ)^1024*1000000000000000^5295 ≤ 1000045818803453^5295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011846839804379367 50000000000000000000 1000045818803453 1000000000000000 1024 5295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000045818803453/1000000000000000 : ℝ)) (X := (50011846839804379367/50000000000000000000 : ℝ)) (by norm_num) 5295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(588763787583681/100000000000000000000 : ℝ) ≤ ((191614833992209021/191625000000000000 : ℝ)+2*(43541593801/153300000000000 : ℝ)*(487/5000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (191614833992209021/191625000000000000 : ℝ)+2*(43541593801/153300000000000 : ℝ)*(487/5000 : ℝ)=(250000569302413/250000000000000 : ℝ) by norm_num, show 1+2*(588763787583681/100000000000000000000 : ℝ)=(50000588763787583681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11846839804379367/100000000000000000000 : ℝ)+(588763787583681/100000000000000000000 : ℝ) ≤ ((191614833992209021/191625000000000000 : ℝ)+(43541593801/153300000000000 : ℝ)*((3481/20000 : ℝ)+(487/5000 : ℝ)))^(5295/1024 : ℝ) := by
    rw [show (191614833992209021/191625000000000000 : ℝ)+(43541593801/153300000000000 : ℝ)*((3481/20000 : ℝ)+(487/5000 : ℝ))=(400009619202621/400000000000000 : ℝ) by norm_num, show 1+(11846839804379367/100000000000000000000 : ℝ)+(588763787583681/100000000000000000000 : ℝ)=(12501554450448995381/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11846839804379367/100000000000000000000 : ℝ) ≤ ((191614833992209021/191625000000000000 : ℝ)+2*(43541593801/153300000000000 : ℝ)*(3481/20000 : ℝ))^(5295/1024 : ℝ) := by
    rw [show (191614833992209021/191625000000000000 : ℝ)+2*(43541593801/153300000000000 : ℝ)*(3481/20000 : ℝ)=(1000045818803453/1000000000000000 : ℝ) by norm_num, show 1+2*(11846839804379367/100000000000000000000 : ℝ)=(50011846839804379367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (191614833992209021/191625000000000000 : ℝ)*(X 1 0+X 2 0)+(43541593801/153300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (487/5000 : ℝ)) (hi := (3481/20000 : ℝ)) (c := (191614833992209021/191625000000000000 : ℝ)) (alpha := (43541593801/153300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (191614833992209021/191625000000000000 : ℝ)*(X 0 1+X 2 1)+(43541593801/153300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (487/5000 : ℝ)) (hi := (3481/20000 : ℝ)) (c := (191614833992209021/191625000000000000 : ℝ)) (alpha := (43541593801/153300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (191614833992209021/191625000000000000 : ℝ)*(X 0 2+X 1 2)+(43541593801/153300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5295/1024 : ℝ)) (lo := (487/5000 : ℝ)) (hi := (3481/20000 : ℝ)) (c := (191614833992209021/191625000000000000 : ℝ)) (alpha := (43541593801/153300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1411937527/10000000000 : ℝ)*X 0 0+(5470560071/10000000000 : ℝ)*X 0 1+(1027571249/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343664943/10000000000 : ℝ)*X 1 0+(-1584472019/10000000000 : ℝ)*X 1 1+(1027571247/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213746603/400000000 : ℝ)*X 2 0+(1284464091/2500000000 : ℝ)*X 2 1+(-198058959/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026152601/2500000000 : ℝ)*X 0 0+(728048487/2000000000 : ℝ)*X 0 1+(4604825721/10000000000 : ℝ)*X 0 2+(1026152601/2500000000 : ℝ)*X 1 0+(728048487/2000000000 : ℝ)*X 1 1+(4604825721/10000000000 : ℝ)*X 1 2+(1026152601/2500000000 : ℝ)*X 2 0+(728048487/2000000000 : ℝ)*X 2 1+(4604825721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-176511227/1250000000 : ℝ)*X 0 0+(5141551491/10000000000 : ℝ)*X 0 1+(683351143/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254608043/10000000000 : ℝ)*X 1 0+(-627759469/5000000000 : ℝ)*X 1 1+(5466809103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328412999/625000000 : ℝ)*X 2 0+(5466809107/10000000000 : ℝ)*X 2 1+(-1255519013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2052525371/5000000000 : ℝ)*X 0 0+(287132023/625000000 : ℝ)*X 0 1+(228194717/625000000 : ℝ)*X 0 2+(2052525371/5000000000 : ℝ)*X 1 0+(287132023/625000000 : ℝ)*X 1 1+(228194717/625000000 : ℝ)*X 1 2+(2052525371/5000000000 : ℝ)*X 2 0+(287132023/625000000 : ℝ)*X 2 1+(228194717/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1710_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20724167931760636788823139/3193750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101991727/20000000000000 : ℝ)*(base19) + (276848901/100000000000000 : ℝ)*(base23) + (10265069/6250000000000 : ℝ)*(lower2) + (86099/625000000000 : ℝ)*(upper3) + (6104809/25000000000000 : ℝ)*(upper5) + (2021203271904541/100000000000000 : ℝ)*(major0) + (2021203271904541/100000000000000 : ℝ)*(major1) + (2021203271904541/100000000000000 : ℝ)*(major2) + (1502840297357589/50000000000000 : ℝ)*(sp0) + (601137422427243/20000000000000 : ℝ)*(sp1) + (3005687345245949/100000000000000 : ℝ)*(sp2) + (259179400780727/25000000000000 : ℝ)*(sp3) + (878422459/12500000000000 : ℝ)*(sp4) + (1102292113/100000000000000 : ℝ)*(sp7) + (1036718705415021/100000000000000 : ℝ)*(f.failure) + (60113752441897/2000000000000 : ℝ)*(f.sum) + (38815695590459/7665000000000000000000000000 : ℝ)*base66 + (5105720643488537/6387500000000000000000000000000 : ℝ)*base67 + (36174563899638537/6387500000000000000000000000000 : ℝ)*base69 + (10754568425251037/6387500000000000000000000000000 : ℝ)*base71 + (11638063255597/3832500000000000000000000000 : ℝ)*base74 + (1346525451823963/6387500000000000000000000000000 : ℝ)*base76 + (8537728321373963/6387500000000000000000000000000 : ℝ)*base78 + (21485053739663537/6387500000000000000000000000000 : ℝ)*base79 + (12465417454801/7665000000000000000000000000 : ℝ)*base81 + (404339/1000000000000000000000 : ℝ)*base89 + (404339/1000000000000000000000 : ℝ)*base91 + (404339/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (806085722171423022655633/114062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (950429209/100000000000000 : ℝ)*(base19) + (15509751/1562500000000 : ℝ)*(base23) + (6499473/5000000000000 : ℝ)*(upper3) + (44622641/100000000000000 : ℝ)*(lower4) + (1300277/781250000000 : ℝ)*(upper5) + (129216700098833/6250000000000 : ℝ)*(major0) + (129216700098833/6250000000000 : ℝ)*(major1) + (129216700098833/6250000000000 : ℝ)*(major2) + (1095342529/12500000000000 : ℝ)*(sp1) + (331144029/4000000000000 : ℝ)*(sp2) + (3074485695881753/100000000000000 : ℝ)*(sp4) + (384309497839039/12500000000000 : ℝ)*(sp5) + (768619106164241/25000000000000 : ℝ)*(sp6) + (265112117928117/25000000000000 : ℝ)*(sp7) + (265112117928117/25000000000000 : ℝ)*(f.failure) + (3074485695881753/100000000000000 : ℝ)*(f.sum) + (2429562322463/479062500000000000000000000 : ℝ)*base65 + (6352083292252699/1596875000000000000000000000000 : ℝ)*base67 + (772881568101669/399218750000000000000000000000 : ℝ)*base70 + (2876293541023331/399218750000000000000000000000 : ℝ)*base71 + (376786411709/958125000000000000000000000 : ℝ)*base74 + (1584435996379581/399218750000000000000000000000 : ℝ)*base75 + (2557296273940199/1596875000000000000000000000000 : ℝ)*base77 + (5418288661285831/399218750000000000000000000000 : ℝ)*base79 + (4005094574833/1916250000000000000000000000 : ℝ)*base82 + (397397/250000000000000000000 : ℝ)*base90 + (397397/250000000000000000000 : ℝ)*base92 + (397397/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1710_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3481/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (487/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1710_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1710_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1710_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1710_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1710_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5295/1024 : ℝ) ≤ p) (hpb : p ≤ (5303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19496159/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1069/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1710_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
