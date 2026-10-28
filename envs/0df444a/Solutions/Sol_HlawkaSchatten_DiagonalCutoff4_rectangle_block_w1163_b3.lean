-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:08.478524+00:00
-- url     : https://prove2.me/submissions/4366761c-eb3c-47f6-baaf-4433340f91ca

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
theorem support_rectangle_w1163_s9_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2156887937/10000000000 : ℝ)*x 0 + (674075363/1250000000 : ℝ)*x 1 + (5266120121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156887937/10000000000 : ℝ)^2089 ≤ (13108207917797/100000000000000 : ℝ)^1577 := by
    have hnat : (2156887937 : ℕ)^2089*100000000000000^1577 ≤ 13108207917797^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156887937 10000000000 13108207917797 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674075363/1250000000 : ℝ)^2089 ≤ (22064405284367/50000000000000 : ℝ)^1577 := by
    have hnat : (674075363 : ℕ)^2089*50000000000000^1577 ≤ 22064405284367^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674075363 1250000000 22064405284367 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266120121/10000000000 : ℝ)^2089 ≤ (42762981500987/100000000000000 : ℝ)^1577 := by
    have hnat : (5266120121 : ℕ)^2089*100000000000000^1577 ≤ 42762981500987^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266120121 10000000000 42762981500987 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2156887937/10000000000 : ℝ), (674075363/1250000000 : ℝ), (5266120121/10000000000 : ℝ)] ![(13108207917797/100000000000000 : ℝ), (22064405284367/50000000000000 : ℝ), (42762981500987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2156887937/10000000000 : ℝ)|^2089 ≤ (13108207917797/100000000000000 : ℝ)^1577
        have hw : |(-2156887937/10000000000 : ℝ)|=(2156887937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674075363/1250000000 : ℝ)|^2089 ≤ (22064405284367/50000000000000 : ℝ)^1577
        have hw : |(674075363/1250000000 : ℝ)|=(674075363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266120121/10000000000 : ℝ)|^2089 ≤ (42762981500987/100000000000000 : ℝ)^1577
        have hw : |(5266120121/10000000000 : ℝ)|=(5266120121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s9_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336166363/2500000000 : ℝ)*x 0 + (-277629267/1250000000 : ℝ)*x 1 + (5266120763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336166363/2500000000 : ℝ)^2089 ≤ (1362809952593/3125000000000 : ℝ)^1577 := by
    have hnat : (1336166363 : ℕ)^2089*3125000000000^1577 ≤ 1362809952593^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336166363 2500000000 1362809952593 3125000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277629267/1250000000 : ℝ)^2089 ≤ (13627093099627/100000000000000 : ℝ)^1577 := by
    have hnat : (277629267 : ℕ)^2089*100000000000000^1577 ≤ 13627093099627^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277629267 1250000000 13627093099627 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266120763/10000000000 : ℝ)^2089 ≤ (21381494203433/50000000000000 : ℝ)^1577 := by
    have hnat : (5266120763 : ℕ)^2089*50000000000000^1577 ≤ 21381494203433^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266120763 10000000000 21381494203433 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336166363/2500000000 : ℝ), (-277629267/1250000000 : ℝ), (5266120763/10000000000 : ℝ)] ![(1362809952593/3125000000000 : ℝ), (13627093099627/100000000000000 : ℝ), (21381494203433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336166363/2500000000 : ℝ)|^2089 ≤ (1362809952593/3125000000000 : ℝ)^1577
        have hw : |(1336166363/2500000000 : ℝ)|=(1336166363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277629267/1250000000 : ℝ)|^2089 ≤ (13627093099627/100000000000000 : ℝ)^1577
        have hw : |(-277629267/1250000000 : ℝ)|=(277629267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266120763/10000000000 : ℝ)|^2089 ≤ (21381494203433/50000000000000 : ℝ)^1577
        have hw : |(5266120763/10000000000 : ℝ)|=(5266120763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s9_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078445287/5000000000 : ℝ)*x 0 + (2633219803/5000000000 : ℝ)*x 1 + (5392283907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078445287/5000000000 : ℝ)^2089 ≤ (1638528643369/12500000000000 : ℝ)^1577 := by
    have hnat : (1078445287 : ℕ)^2089*12500000000000^1577 ≤ 1638528643369^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078445287 5000000000 1638528643369 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633219803/5000000000 : ℝ)^2089 ≤ (8553283635591/20000000000000 : ℝ)^1577 := by
    have hnat : (2633219803 : ℕ)^2089*20000000000000^1577 ≤ 8553283635591^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633219803 5000000000 8553283635591 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392283907/10000000000 : ℝ)^2089 ≤ (11031338166137/25000000000000 : ℝ)^1577 := by
    have hnat : (5392283907 : ℕ)^2089*25000000000000^1577 ≤ 11031338166137^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392283907 10000000000 11031338166137 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078445287/5000000000 : ℝ), (2633219803/5000000000 : ℝ), (5392283907/10000000000 : ℝ)] ![(1638528643369/12500000000000 : ℝ), (8553283635591/20000000000000 : ℝ), (11031338166137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078445287/5000000000 : ℝ)|^2089 ≤ (1638528643369/12500000000000 : ℝ)^1577
        have hw : |(-1078445287/5000000000 : ℝ)|=(1078445287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633219803/5000000000 : ℝ)|^2089 ≤ (8553283635591/20000000000000 : ℝ)^1577
        have hw : |(2633219803/5000000000 : ℝ)|=(2633219803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392283907/10000000000 : ℝ)|^2089 ≤ (11031338166137/25000000000000 : ℝ)^1577
        have hw : |(5392283907/10000000000 : ℝ)|=(5392283907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s9_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312570811/10000000000 : ℝ)*x 0 + (-2094871451/10000000000 : ℝ)*x 1 + (2696141943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312570811/10000000000 : ℝ)^2089 ≤ (21631678664043/50000000000000 : ℝ)^1577 := by
    have hnat : (5312570811 : ℕ)^2089*50000000000000^1577 ≤ 21631678664043^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312570811 10000000000 21631678664043 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094871451/10000000000 : ℝ)^2089 ≤ (6305645109067/50000000000000 : ℝ)^1577 := by
    have hnat : (2094871451 : ℕ)^2089*50000000000000^1577 ≤ 6305645109067^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094871451 10000000000 6305645109067 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696141943/5000000000 : ℝ)^2089 ≤ (44125352436911/100000000000000 : ℝ)^1577 := by
    have hnat : (2696141943 : ℕ)^2089*100000000000000^1577 ≤ 44125352436911^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696141943 5000000000 44125352436911 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312570811/10000000000 : ℝ), (-2094871451/10000000000 : ℝ), (2696141943/5000000000 : ℝ)] ![(21631678664043/50000000000000 : ℝ), (6305645109067/50000000000000 : ℝ), (44125352436911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312570811/10000000000 : ℝ)|^2089 ≤ (21631678664043/50000000000000 : ℝ)^1577
        have hw : |(5312570811/10000000000 : ℝ)|=(5312570811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094871451/10000000000 : ℝ)|^2089 ≤ (6305645109067/50000000000000 : ℝ)^1577
        have hw : |(-2094871451/10000000000 : ℝ)|=(2094871451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696141943/5000000000 : ℝ)|^2089 ≤ (44125352436911/100000000000000 : ℝ)^1577
        have hw : |(2696141943/5000000000 : ℝ)|=(2696141943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s9_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312570891/10000000000 : ℝ)*x 0 + (1348070933/2500000000 : ℝ)*x 1 + (-2094871553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312570891/10000000000 : ℝ)^2089 ≤ (43263358191089/100000000000000 : ℝ)^1577 := by
    have hnat : (5312570891 : ℕ)^2089*100000000000000^1577 ≤ 43263358191089^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312570891 10000000000 43263358191089 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348070933/2500000000 : ℝ)^2089 ≤ (44125350767579/100000000000000 : ℝ)^1577 := by
    have hnat : (1348070933 : ℕ)^2089*100000000000000^1577 ≤ 44125350767579^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348070933 2500000000 44125350767579 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094871553/10000000000 : ℝ)^2089 ≤ (12611291031543/100000000000000 : ℝ)^1577 := by
    have hnat : (2094871553 : ℕ)^2089*100000000000000^1577 ≤ 12611291031543^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094871553 10000000000 12611291031543 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312570891/10000000000 : ℝ), (1348070933/2500000000 : ℝ), (-2094871553/10000000000 : ℝ)] ![(43263358191089/100000000000000 : ℝ), (44125350767579/100000000000000 : ℝ), (12611291031543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312570891/10000000000 : ℝ)|^2089 ≤ (43263358191089/100000000000000 : ℝ)^1577
        have hw : |(5312570891/10000000000 : ℝ)|=(5312570891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348070933/2500000000 : ℝ)|^2089 ≤ (44125350767579/100000000000000 : ℝ)^1577
        have hw : |(1348070933/2500000000 : ℝ)|=(1348070933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094871553/10000000000 : ℝ)|^2089 ≤ (12611291031543/100000000000000 : ℝ)^1577
        have hw : |(-2094871553/10000000000 : ℝ)|=(2094871553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_s9_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (218086757/500000000 : ℝ)*x 0 + (4489236159/10000000000 : ℝ)*x 1 + (2118920399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218086757/500000000 : ℝ)^2089 ≤ (1041162559487/3125000000000 : ℝ)^1577 := by
    have hnat : (218086757 : ℕ)^2089*3125000000000^1577 ≤ 1041162559487^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218086757 500000000 1041162559487 3125000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489236159/10000000000 : ℝ)^2089 ≤ (17306701339139/50000000000000 : ℝ)^1577 := by
    have hnat : (4489236159 : ℕ)^2089*50000000000000^1577 ≤ 17306701339139^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489236159 10000000000 17306701339139 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118920399/5000000000 : ℝ)^2089 ≤ (4008674425559/12500000000000 : ℝ)^1577 := by
    have hnat : (2118920399 : ℕ)^2089*12500000000000^1577 ≤ 4008674425559^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118920399 5000000000 4008674425559 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218086757/500000000 : ℝ), (4489236159/10000000000 : ℝ), (2118920399/5000000000 : ℝ)] ![(1041162559487/3125000000000 : ℝ), (17306701339139/50000000000000 : ℝ), (4008674425559/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218086757/500000000 : ℝ)|^2089 ≤ (1041162559487/3125000000000 : ℝ)^1577
        have hw : |(218086757/500000000 : ℝ)|=(218086757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489236159/10000000000 : ℝ)|^2089 ≤ (17306701339139/50000000000000 : ℝ)^1577
        have hw : |(4489236159/10000000000 : ℝ)|=(4489236159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118920399/5000000000 : ℝ)|^2089 ≤ (4008674425559/12500000000000 : ℝ)^1577
        have hw : |(2118920399/5000000000 : ℝ)|=(2118920399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11381/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (11381/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (441014899748799/3125000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^8355 ≤ (441014899748799/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11381 : ℕ)^8355*3125000000000000000^2048 ≤ 441014899748799^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 441014899748799 3125000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (441014899748799/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (33439176691073823/100000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^8355 ≤ (33439176691073823/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14061 : ℕ)^8355*100000000000000000000^2048 ≤ 33439176691073823^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 33439176691073823 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (33439176691073823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562941014899748799/1562500000000000000 : ℝ) ≤ (10000691783936711/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (1562941014899748799/1562500000000000000 : ℝ)^2048 ≤ (10000691783936711/10000000000000000 : ℝ)^8355 := by
      have hnat : (1562941014899748799 : ℕ)^2048*10000000000000000^8355 ≤ 10000691783936711^8355*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562941014899748799 1562500000000000000 10000691783936711 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000691783936711/10000000000000000 : ℝ)) (X := (1562941014899748799/1562500000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047551653483035391/100000000000000000000 : ℝ) ≤ (10001165389737353/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100047551653483035391/100000000000000000000 : ℝ)^2048 ≤ (10001165389737353/10000000000000000 : ℝ)^8355 := by
      have hnat : (100047551653483035391 : ℕ)^2048*10000000000000000^8355 ≤ 10001165389737353^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047551653483035391 100000000000000000000 10001165389737353 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001165389737353/10000000000000000 : ℝ)) (X := (100047551653483035391/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033439176691073823/50000000000000000000 : ℝ) ≤ (2000327799107599/2000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50033439176691073823/50000000000000000000 : ℝ)^2048 ≤ (2000327799107599/2000000000000000 : ℝ)^8355 := by
      have hnat : (50033439176691073823 : ℕ)^2048*2000000000000000^8355 ≤ 2000327799107599^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033439176691073823 50000000000000000000 2000327799107599 2000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000327799107599/2000000000000000 : ℝ)) (X := (50033439176691073823/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(441014899748799/3125000000000000000 : ℝ) ≤ ((6697768441429043069/6700000000000000000 : ℝ)+2*(236802900321/134000000000000 : ℝ)*(11381/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (6697768441429043069/6700000000000000000 : ℝ)+2*(236802900321/134000000000000 : ℝ)*(11381/100000 : ℝ)=(10000691783936711/10000000000000000 : ℝ) by norm_num, show 1+2*(441014899748799/3125000000000000000 : ℝ)=(1562941014899748799/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33439176691073823/100000000000000000000 : ℝ)+(441014899748799/3125000000000000000 : ℝ) ≤ ((6697768441429043069/6700000000000000000 : ℝ)+(236802900321/134000000000000 : ℝ)*((14061/100000 : ℝ)+(11381/100000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (6697768441429043069/6700000000000000000 : ℝ)+(236802900321/134000000000000 : ℝ)*((14061/100000 : ℝ)+(11381/100000 : ℝ))=(10001165389737353/10000000000000000 : ℝ) by norm_num, show 1+(33439176691073823/100000000000000000000 : ℝ)+(441014899748799/3125000000000000000 : ℝ)=(100047551653483035391/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33439176691073823/100000000000000000000 : ℝ) ≤ ((6697768441429043069/6700000000000000000 : ℝ)+2*(236802900321/134000000000000 : ℝ)*(14061/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (6697768441429043069/6700000000000000000 : ℝ)+2*(236802900321/134000000000000 : ℝ)*(14061/100000 : ℝ)=(2000327799107599/2000000000000000 : ℝ) by norm_num, show 1+2*(33439176691073823/100000000000000000000 : ℝ)=(50033439176691073823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6697768441429043069/6700000000000000000 : ℝ)*(X 1 0+X 2 0)+(236802900321/134000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (6697768441429043069/6700000000000000000 : ℝ)) (alpha := (236802900321/134000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6697768441429043069/6700000000000000000 : ℝ)*(X 0 1+X 2 1)+(236802900321/134000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (6697768441429043069/6700000000000000000 : ℝ)) (alpha := (236802900321/134000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6697768441429043069/6700000000000000000 : ℝ)*(X 0 2+X 1 2)+(236802900321/134000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (6697768441429043069/6700000000000000000 : ℝ)) (alpha := (236802900321/134000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2156887937/10000000000 : ℝ)*X 0 0+(674075363/1250000000 : ℝ)*X 0 1+(5266120121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336166363/2500000000 : ℝ)*X 1 0+(-277629267/1250000000 : ℝ)*X 1 1+(5266120763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1078445287/5000000000 : ℝ)*X 0 0+(2633219803/5000000000 : ℝ)*X 0 1+(5392283907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312570811/10000000000 : ℝ)*X 1 0+(-2094871451/10000000000 : ℝ)*X 1 1+(2696141943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312570891/10000000000 : ℝ)*X 2 0+(1348070933/2500000000 : ℝ)*X 2 1+(-2094871553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((218086757/500000000 : ℝ)*X 0 0+(4489236159/10000000000 : ℝ)*X 0 1+(2118920399/5000000000 : ℝ)*X 0 2+(218086757/500000000 : ℝ)*X 1 0+(4489236159/10000000000 : ℝ)*X 1 1+(2118920399/5000000000 : ℝ)*X 1 2+(218086757/500000000 : ℝ)*X 2 0+(4489236159/10000000000 : ℝ)*X 2 1+(2118920399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5788764804854769292527/1340000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22128511/25000000000000 : ℝ)*(base8) + (6420617/50000000000000 : ℝ)*(upper1) + (84328771/100000000000000 : ℝ)*(lower2) + (3823093/6250000000000 : ℝ)*(upper3) + (39294523/100000000000000 : ℝ)*(lower4) + (1192414267816717/20000000000000 : ℝ)*(major0) + (1192414267816717/20000000000000 : ℝ)*(major1) + (1192414267816717/20000000000000 : ℝ)*(major2) + (1429137373/20000000000000 : ℝ)*(sp0) + (5775570721/100000000000000 : ℝ)*(sp1) + (794633453918909/10000000000000 : ℝ)*(sp2) + (3973167998909639/50000000000000 : ℝ)*(sp3) + (7946341773389999/100000000000000 : ℝ)*(sp4) + (1988900380389021/50000000000000 : ℝ)*(sp5) + (1988900380389021/50000000000000 : ℝ)*(f.failure) + (7946341773389999/100000000000000 : ℝ)*(f.sum) + (13841572108057/1340000000000000000000000000 : ℝ)*base65 + (228563618647034473/134000000000000000000000000000000 : ℝ)*base67 + (774658155825034473/134000000000000000000000000000000 : ℝ)*base69 + (1135696552320965527/134000000000000000000000000000000 : ℝ)*base72 + (2923861099197/1340000000000000000000000000 : ℝ)*base73 + (157130828398965527/134000000000000000000000000000000 : ℝ)*base76 + (199116116026965527/134000000000000000000000000000000 : ℝ)*base78 + (211620421735034473/134000000000000000000000000000000 : ℝ)*base79 + (5371367313697/1340000000000000000000000000 : ℝ)*base81 + (41456789/5000000000000000000000 : ℝ)*base89 + (41456789/5000000000000000000000 : ℝ)*base91 + (41456789/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1163_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1163_box_0 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-203068663/1000000000 : ℝ)*x 0 + (5376006839/10000000000 : ℝ)*x 1 + (2688003287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203068663/1000000000 : ℝ)^2089 ≤ (12102005556993/100000000000000 : ℝ)^1577 := by
    have hnat : (203068663 : ℕ)^2089*100000000000000^1577 ≤ 12102005556993^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203068663 1000000000 12102005556993 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376006839/10000000000 : ℝ)^2089 ≤ (43948998648179/100000000000000 : ℝ)^1577 := by
    have hnat : (5376006839 : ℕ)^2089*100000000000000^1577 ≤ 43948998648179^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376006839 10000000000 43948998648179 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688003287/5000000000 : ℝ)^2089 ≤ (10987248944611/25000000000000 : ℝ)^1577 := by
    have hnat : (2688003287 : ℕ)^2089*25000000000000^1577 ≤ 10987248944611^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688003287 5000000000 10987248944611 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203068663/1000000000 : ℝ), (5376006839/10000000000 : ℝ), (2688003287/5000000000 : ℝ)] ![(12102005556993/100000000000000 : ℝ), (43948998648179/100000000000000 : ℝ), (10987248944611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203068663/1000000000 : ℝ)|^2089 ≤ (12102005556993/100000000000000 : ℝ)^1577
        have hw : |(-203068663/1000000000 : ℝ)|=(203068663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376006839/10000000000 : ℝ)|^2089 ≤ (43948998648179/100000000000000 : ℝ)^1577
        have hw : |(5376006839/10000000000 : ℝ)|=(5376006839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688003287/5000000000 : ℝ)|^2089 ≤ (10987248944611/25000000000000 : ℝ)^1577
        have hw : |(2688003287/5000000000 : ℝ)|=(2688003287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_1 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1324044031/2500000000 : ℝ)*x 0 + (-85560153/400000000 : ℝ)*x 1 + (5376005681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324044031/2500000000 : ℝ)^2089 ≤ (1346455866349/3125000000000 : ℝ)^1577 := by
    have hnat : (1324044031 : ℕ)^2089*3125000000000^1577 ≤ 1346455866349^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324044031 2500000000 1346455866349 3125000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85560153/400000000 : ℝ)^2089 ≤ (12964426152003/100000000000000 : ℝ)^1577 := by
    have hnat : (85560153 : ℕ)^2089*100000000000000^1577 ≤ 12964426152003^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85560153 400000000 12964426152003 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376005681/10000000000 : ℝ)^2089 ≤ (43948986107979/100000000000000 : ℝ)^1577 := by
    have hnat : (5376005681 : ℕ)^2089*100000000000000^1577 ≤ 43948986107979^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376005681 10000000000 43948986107979 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324044031/2500000000 : ℝ), (-85560153/400000000 : ℝ), (5376005681/10000000000 : ℝ)] ![(1346455866349/3125000000000 : ℝ), (12964426152003/100000000000000 : ℝ), (43948986107979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324044031/2500000000 : ℝ)|^2089 ≤ (1346455866349/3125000000000 : ℝ)^1577
        have hw : |(1324044031/2500000000 : ℝ)|=(1324044031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85560153/400000000 : ℝ)|^2089 ≤ (12964426152003/100000000000000 : ℝ)^1577
        have hw : |(-85560153/400000000 : ℝ)|=(85560153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376005681/10000000000 : ℝ)|^2089 ≤ (43948986107979/100000000000000 : ℝ)^1577
        have hw : |(5376005681/10000000000 : ℝ)|=(5376005681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_2 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1324044289/2500000000 : ℝ)*x 0 + (672000659/1250000000 : ℝ)*x 1 + (-133687687/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324044289/2500000000 : ℝ)^2089 ≤ (43086598844739/100000000000000 : ℝ)^1577 := by
    have hnat : (1324044289 : ℕ)^2089*100000000000000^1577 ≤ 43086598844739^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324044289 2500000000 43086598844739 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672000659/1250000000 : ℝ)^2089 ≤ (43948981678841/100000000000000 : ℝ)^1577 := by
    have hnat : (672000659 : ℕ)^2089*100000000000000^1577 ≤ 43948981678841^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672000659 1250000000 43948981678841 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133687687/625000000 : ℝ)^2089 ≤ (12964419464047/100000000000000 : ℝ)^1577 := by
    have hnat : (133687687 : ℕ)^2089*100000000000000^1577 ≤ 12964419464047^1577*625000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133687687 625000000 12964419464047 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324044289/2500000000 : ℝ), (672000659/1250000000 : ℝ), (-133687687/625000000 : ℝ)] ![(43086598844739/100000000000000 : ℝ), (43948981678841/100000000000000 : ℝ), (12964419464047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324044289/2500000000 : ℝ)|^2089 ≤ (43086598844739/100000000000000 : ℝ)^1577
        have hw : |(1324044289/2500000000 : ℝ)|=(1324044289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672000659/1250000000 : ℝ)|^2089 ≤ (43948981678841/100000000000000 : ℝ)^1577
        have hw : |(672000659/1250000000 : ℝ)|=(672000659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133687687/625000000 : ℝ)|^2089 ≤ (12964419464047/100000000000000 : ℝ)^1577
        have hw : |(-133687687/625000000 : ℝ)|=(133687687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_3 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2234521321/5000000000 : ℝ)*x 0 + (215508023/500000000 : ℝ)*x 1 + (4310160339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2234521321/5000000000 : ℝ)^2089 ≤ (17203652526081/50000000000000 : ℝ)^1577 := by
    have hnat : (2234521321 : ℕ)^2089*50000000000000^1577 ≤ 17203652526081^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234521321 5000000000 17203652526081 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215508023/500000000 : ℝ)^2089 ≤ (16398174037661/50000000000000 : ℝ)^1577 := by
    have hnat : (215508023 : ℕ)^2089*50000000000000^1577 ≤ 16398174037661^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215508023 500000000 16398174037661 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4310160339/10000000000 : ℝ)^2089 ≤ (32796346855703/100000000000000 : ℝ)^1577 := by
    have hnat : (4310160339 : ℕ)^2089*100000000000000^1577 ≤ 32796346855703^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310160339 10000000000 32796346855703 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2234521321/5000000000 : ℝ), (215508023/500000000 : ℝ), (4310160339/10000000000 : ℝ)] ![(17203652526081/50000000000000 : ℝ), (16398174037661/50000000000000 : ℝ), (32796346855703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2234521321/5000000000 : ℝ)|^2089 ≤ (17203652526081/50000000000000 : ℝ)^1577
        have hw : |(2234521321/5000000000 : ℝ)|=(2234521321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215508023/500000000 : ℝ)|^2089 ≤ (16398174037661/50000000000000 : ℝ)^1577
        have hw : |(215508023/500000000 : ℝ)|=(215508023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4310160339/10000000000 : ℝ)|^2089 ≤ (32796346855703/100000000000000 : ℝ)^1577
        have hw : |(4310160339/10000000000 : ℝ)|=(4310160339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_4 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2284473637/10000000000 : ℝ)*x 0 + (528140399/1000000000 : ℝ)*x 1 + (5281403987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2284473637/10000000000 : ℝ)^2089 ≤ (14145070503667/100000000000000 : ℝ)^1577 := by
    have hnat : (2284473637 : ℕ)^2089*100000000000000^1577 ≤ 14145070503667^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284473637 10000000000 14145070503667 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528140399/1000000000 : ℝ)^2089 ≤ (42927464759717/100000000000000 : ℝ)^1577 := by
    have hnat : (528140399 : ℕ)^2089*100000000000000^1577 ≤ 42927464759717^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528140399 1000000000 42927464759717 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281403987/10000000000 : ℝ)^2089 ≤ (5365933090927/12500000000000 : ℝ)^1577 := by
    have hnat : (5281403987 : ℕ)^2089*12500000000000^1577 ≤ 5365933090927^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281403987 10000000000 5365933090927 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2284473637/10000000000 : ℝ), (528140399/1000000000 : ℝ), (5281403987/10000000000 : ℝ)] ![(14145070503667/100000000000000 : ℝ), (42927464759717/100000000000000 : ℝ), (5365933090927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2284473637/10000000000 : ℝ)|^2089 ≤ (14145070503667/100000000000000 : ℝ)^1577
        have hw : |(-2284473637/10000000000 : ℝ)|=(2284473637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528140399/1000000000 : ℝ)|^2089 ≤ (42927464759717/100000000000000 : ℝ)^1577
        have hw : |(528140399/1000000000 : ℝ)|=(528140399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281403987/10000000000 : ℝ)|^2089 ≤ (5365933090927/12500000000000 : ℝ)^1577
        have hw : |(5281403987/10000000000 : ℝ)|=(5281403987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_5 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362980267/10000000000 : ℝ)*x 0 + (-2176279761/10000000000 : ℝ)*x 1 + (1320350979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362980267/10000000000 : ℝ)^2089 ≤ (8761597392367/20000000000000 : ℝ)^1577 := by
    have hnat : (5362980267 : ℕ)^2089*20000000000000^1577 ≤ 8761597392367^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362980267 10000000000 8761597392367 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176279761/10000000000 : ℝ)^2089 ≤ (13264549050799/100000000000000 : ℝ)^1577 := by
    have hnat : (2176279761 : ℕ)^2089*100000000000000^1577 ≤ 13264549050799^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176279761 10000000000 13264549050799 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320350979/2500000000 : ℝ)^2089 ≤ (42927463962963/100000000000000 : ℝ)^1577 := by
    have hnat : (1320350979 : ℕ)^2089*100000000000000^1577 ≤ 42927463962963^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320350979 2500000000 42927463962963 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362980267/10000000000 : ℝ), (-2176279761/10000000000 : ℝ), (1320350979/2500000000 : ℝ)] ![(8761597392367/20000000000000 : ℝ), (13264549050799/100000000000000 : ℝ), (42927463962963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362980267/10000000000 : ℝ)|^2089 ≤ (8761597392367/20000000000000 : ℝ)^1577
        have hw : |(5362980267/10000000000 : ℝ)|=(5362980267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176279761/10000000000 : ℝ)|^2089 ≤ (13264549050799/100000000000000 : ℝ)^1577
        have hw : |(-2176279761/10000000000 : ℝ)|=(2176279761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320350979/2500000000 : ℝ)|^2089 ≤ (42927463962963/100000000000000 : ℝ)^1577
        have hw : |(1320350979/2500000000 : ℝ)|=(1320350979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_6 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362980097/10000000000 : ℝ)*x 0 + (264070199/500000000 : ℝ)*x 1 + (-68008747/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362980097/10000000000 : ℝ)^2089 ≤ (43807985122323/100000000000000 : ℝ)^1577 := by
    have hnat : (5362980097 : ℕ)^2089*100000000000000^1577 ≤ 43807985122323^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362980097 10000000000 43807985122323 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264070199/500000000 : ℝ)^2089 ≤ (2682966540753/6250000000000 : ℝ)^1577 := by
    have hnat : (264070199 : ℕ)^2089*6250000000000^1577 ≤ 2682966540753^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264070199 500000000 2682966540753 6250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68008747/312500000 : ℝ)^2089 ≤ (1326455020537/10000000000000 : ℝ)^1577 := by
    have hnat : (68008747 : ℕ)^2089*10000000000000^1577 ≤ 1326455020537^1577*312500000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68008747 312500000 1326455020537 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362980097/10000000000 : ℝ), (264070199/500000000 : ℝ), (-68008747/312500000 : ℝ)] ![(43807985122323/100000000000000 : ℝ), (2682966540753/6250000000000 : ℝ), (1326455020537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362980097/10000000000 : ℝ)|^2089 ≤ (43807985122323/100000000000000 : ℝ)^1577
        have hw : |(5362980097/10000000000 : ℝ)|=(5362980097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264070199/500000000 : ℝ)|^2089 ≤ (2682966540753/6250000000000 : ℝ)^1577
        have hw : |(264070199/500000000 : ℝ)|=(264070199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68008747/312500000 : ℝ)|^2089 ≤ (1326455020537/10000000000000 : ℝ)^1577
        have hw : |(-68008747/312500000 : ℝ)|=(68008747/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_7 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2127018133/5000000000 : ℝ)*x 0 + (552205371/1250000000 : ℝ)*x 1 + (4417642833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127018133/5000000000 : ℝ)^2089 ≤ (257854750609/800000000000 : ℝ)^1577 := by
    have hnat : (2127018133 : ℕ)^2089*800000000000^1577 ≤ 257854750609^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127018133 5000000000 257854750609 800000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552205371/1250000000 : ℝ)^2089 ≤ (16942039383721/50000000000000 : ℝ)^1577 := by
    have hnat : (552205371 : ℕ)^2089*50000000000000^1577 ≤ 16942039383721^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552205371 1250000000 16942039383721 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417642833/10000000000 : ℝ)^2089 ≤ (6776815479157/20000000000000 : ℝ)^1577 := by
    have hnat : (4417642833 : ℕ)^2089*20000000000000^1577 ≤ 6776815479157^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417642833 10000000000 6776815479157 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127018133/5000000000 : ℝ), (552205371/1250000000 : ℝ), (4417642833/10000000000 : ℝ)] ![(257854750609/800000000000 : ℝ), (16942039383721/50000000000000 : ℝ), (6776815479157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127018133/5000000000 : ℝ)|^2089 ≤ (257854750609/800000000000 : ℝ)^1577
        have hw : |(2127018133/5000000000 : ℝ)|=(2127018133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552205371/1250000000 : ℝ)|^2089 ≤ (16942039383721/50000000000000 : ℝ)^1577
        have hw : |(552205371/1250000000 : ℝ)|=(552205371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417642833/10000000000 : ℝ)|^2089 ≤ (6776815479157/20000000000000 : ℝ)^1577
        have hw : |(4417642833/10000000000 : ℝ)|=(4417642833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_8 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-11156897/50000000 : ℝ)*x 0 + (5217024667/10000000000 : ℝ)*x 1 + (5385616279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11156897/50000000 : ℝ)^2089 ≤ (13711237307871/100000000000000 : ℝ)^1577 := by
    have hnat : (11156897 : ℕ)^2089*100000000000000^1577 ≤ 13711237307871^1577*50000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11156897 50000000 13711237307871 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217024667/10000000000 : ℝ)^2089 ≤ (42235671401431/100000000000000 : ℝ)^1577 := by
    have hnat : (5217024667 : ℕ)^2089*100000000000000^1577 ≤ 42235671401431^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217024667 10000000000 42235671401431 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385616279/10000000000 : ℝ)^2089 ≤ (8810618253957/20000000000000 : ℝ)^1577 := by
    have hnat : (5385616279 : ℕ)^2089*20000000000000^1577 ≤ 8810618253957^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385616279 10000000000 8810618253957 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11156897/50000000 : ℝ), (5217024667/10000000000 : ℝ), (5385616279/10000000000 : ℝ)] ![(13711237307871/100000000000000 : ℝ), (42235671401431/100000000000000 : ℝ), (8810618253957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11156897/50000000 : ℝ)|^2089 ≤ (13711237307871/100000000000000 : ℝ)^1577
        have hw : |(-11156897/50000000 : ℝ)|=(11156897/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217024667/10000000000 : ℝ)|^2089 ≤ (42235671401431/100000000000000 : ℝ)^1577
        have hw : |(5217024667/10000000000 : ℝ)|=(5217024667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385616279/10000000000 : ℝ)|^2089 ≤ (8810618253957/20000000000000 : ℝ)^1577
        have hw : |(5385616279/10000000000 : ℝ)|=(5385616279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_9 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644693107/5000000000 : ℝ)*x 0 + (-2135149063/10000000000 : ℝ)*x 1 + (269280779/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644693107/5000000000 : ℝ)^2089 ≤ (43013430026009/100000000000000 : ℝ)^1577 := by
    have hnat : (2644693107 : ℕ)^2089*100000000000000^1577 ≤ 43013430026009^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644693107 5000000000 43013430026009 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135149063/10000000000 : ℝ)^2089 ≤ (1616685781271/12500000000000 : ℝ)^1577 := by
    have hnat : (2135149063 : ℕ)^2089*12500000000000^1577 ≤ 1616685781271^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135149063 10000000000 1616685781271 12500000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269280779/500000000 : ℝ)^2089 ≤ (2753317730987/6250000000000 : ℝ)^1577 := by
    have hnat : (269280779 : ℕ)^2089*6250000000000^1577 ≤ 2753317730987^1577*500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269280779 500000000 2753317730987 6250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644693107/5000000000 : ℝ), (-2135149063/10000000000 : ℝ), (269280779/500000000 : ℝ)] ![(43013430026009/100000000000000 : ℝ), (1616685781271/12500000000000 : ℝ), (2753317730987/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644693107/5000000000 : ℝ)|^2089 ≤ (43013430026009/100000000000000 : ℝ)^1577
        have hw : |(2644693107/5000000000 : ℝ)|=(2644693107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135149063/10000000000 : ℝ)|^2089 ≤ (1616685781271/12500000000000 : ℝ)^1577
        have hw : |(-2135149063/10000000000 : ℝ)|=(2135149063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269280779/500000000 : ℝ)|^2089 ≤ (2753317730987/6250000000000 : ℝ)^1577
        have hw : |(269280779/500000000 : ℝ)|=(269280779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_10 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289385741/10000000000 : ℝ)*x 0 + (168300491/312500000 : ℝ)*x 1 + (-26689369/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289385741/10000000000 : ℝ)^2089 ≤ (8602684986149/20000000000000 : ℝ)^1577 := by
    have hnat : (5289385741 : ℕ)^2089*20000000000000^1577 ≤ 8602684986149^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289385741 10000000000 8602684986149 20000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168300491/312500000 : ℝ)^2089 ≤ (22026542563037/50000000000000 : ℝ)^1577 := by
    have hnat : (168300491 : ℕ)^2089*50000000000000^1577 ≤ 22026542563037^1577*312500000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168300491 312500000 22026542563037 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26689369/125000000 : ℝ)^2089 ≤ (3233372479291/25000000000000 : ℝ)^1577 := by
    have hnat : (26689369 : ℕ)^2089*25000000000000^1577 ≤ 3233372479291^1577*125000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26689369 125000000 3233372479291 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289385741/10000000000 : ℝ), (168300491/312500000 : ℝ), (-26689369/125000000 : ℝ)] ![(8602684986149/20000000000000 : ℝ), (22026542563037/50000000000000 : ℝ), (3233372479291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289385741/10000000000 : ℝ)|^2089 ≤ (8602684986149/20000000000000 : ℝ)^1577
        have hw : |(5289385741/10000000000 : ℝ)|=(5289385741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168300491/312500000 : ℝ)|^2089 ≤ (22026542563037/50000000000000 : ℝ)^1577
        have hw : |(168300491/312500000 : ℝ)|=(168300491/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26689369/125000000 : ℝ)|^2089 ≤ (3233372479291/25000000000000 : ℝ)^1577
        have hw : |(-26689369/125000000 : ℝ)|=(26689369/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_11 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (112265313/250000000 : ℝ)*x 0 + (429923477/1000000000 : ℝ)*x 1 + (171969403/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112265313/250000000 : ℝ)^2089 ≤ (8656865242573/25000000000000 : ℝ)^1577 := by
    have hnat : (112265313 : ℕ)^2089*25000000000000^1577 ≤ 8656865242573^1577*250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112265313 250000000 8656865242573 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429923477/1000000000 : ℝ)^2089 ≤ (3268626797403/10000000000000 : ℝ)^1577 := by
    have hnat : (429923477 : ℕ)^2089*10000000000000^1577 ≤ 3268626797403^1577*1000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429923477 1000000000 3268626797403 10000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171969403/400000000 : ℝ)^2089 ≤ (2042891940359/6250000000000 : ℝ)^1577 := by
    have hnat : (171969403 : ℕ)^2089*6250000000000^1577 ≤ 2042891940359^1577*400000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171969403 400000000 2042891940359 6250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112265313/250000000 : ℝ), (429923477/1000000000 : ℝ), (171969403/400000000 : ℝ)] ![(8656865242573/25000000000000 : ℝ), (3268626797403/10000000000000 : ℝ), (2042891940359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112265313/250000000 : ℝ)|^2089 ≤ (8656865242573/25000000000000 : ℝ)^1577
        have hw : |(112265313/250000000 : ℝ)|=(112265313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(429923477/1000000000 : ℝ)|^2089 ≤ (3268626797403/10000000000000 : ℝ)^1577
        have hw : |(429923477/1000000000 : ℝ)|=(429923477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171969403/400000000 : ℝ)|^2089 ≤ (2042891940359/6250000000000 : ℝ)^1577
        have hw : |(171969403/400000000 : ℝ)|=(171969403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_12 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084088339/10000000000 : ℝ)*x 0 + (5439122501/10000000000 : ℝ)*x 1 + (2636678263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084088339/10000000000 : ℝ)^2089 ≤ (3131342788519/25000000000000 : ℝ)^1577 := by
    have hnat : (2084088339 : ℕ)^2089*25000000000000^1577 ≤ 3131342788519^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084088339 10000000000 3131342788519 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439122501/10000000000 : ℝ)^2089 ≤ (22316894627127/50000000000000 : ℝ)^1577 := by
    have hnat : (5439122501 : ℕ)^2089*50000000000000^1577 ≤ 22316894627127^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439122501 10000000000 22316894627127 50000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636678263/5000000000 : ℝ)^2089 ≤ (2142041978827/5000000000000 : ℝ)^1577 := by
    have hnat : (2636678263 : ℕ)^2089*5000000000000^1577 ≤ 2142041978827^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636678263 5000000000 2142041978827 5000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084088339/10000000000 : ℝ), (5439122501/10000000000 : ℝ), (2636678263/5000000000 : ℝ)] ![(3131342788519/25000000000000 : ℝ), (22316894627127/50000000000000 : ℝ), (2142041978827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084088339/10000000000 : ℝ)|^2089 ≤ (3131342788519/25000000000000 : ℝ)^1577
        have hw : |(-2084088339/10000000000 : ℝ)|=(2084088339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439122501/10000000000 : ℝ)|^2089 ≤ (22316894627127/50000000000000 : ℝ)^1577
        have hw : |(5439122501/10000000000 : ℝ)|=(5439122501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636678263/5000000000 : ℝ)|^2089 ≤ (2142041978827/5000000000000 : ℝ)^1577
        have hw : |(2636678263/5000000000 : ℝ)|=(2636678263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_13 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671082633/1250000000 : ℝ)*x 0 + (-1089696651/5000000000 : ℝ)*x 1 + (5273356481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671082633/1250000000 : ℝ)^2089 ≤ (43869467515437/100000000000000 : ℝ)^1577 := by
    have hnat : (671082633 : ℕ)^2089*100000000000000^1577 ≤ 43869467515437^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671082633 1250000000 43869467515437 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089696651/5000000000 : ℝ)^2089 ≤ (531587734893/4000000000000 : ℝ)^1577 := by
    have hnat : (1089696651 : ℕ)^2089*4000000000000^1577 ≤ 531587734893^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089696651 5000000000 531587734893 4000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273356481/10000000000 : ℝ)^2089 ≤ (42840839092267/100000000000000 : ℝ)^1577 := by
    have hnat : (5273356481 : ℕ)^2089*100000000000000^1577 ≤ 42840839092267^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273356481 10000000000 42840839092267 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671082633/1250000000 : ℝ), (-1089696651/5000000000 : ℝ), (5273356481/10000000000 : ℝ)] ![(43869467515437/100000000000000 : ℝ), (531587734893/4000000000000 : ℝ), (42840839092267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671082633/1250000000 : ℝ)|^2089 ≤ (43869467515437/100000000000000 : ℝ)^1577
        have hw : |(671082633/1250000000 : ℝ)|=(671082633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089696651/5000000000 : ℝ)|^2089 ≤ (531587734893/4000000000000 : ℝ)^1577
        have hw : |(-1089696651/5000000000 : ℝ)|=(1089696651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273356481/10000000000 : ℝ)|^2089 ≤ (42840839092267/100000000000000 : ℝ)^1577
        have hw : |(5273356481/10000000000 : ℝ)|=(5273356481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_14 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684330389/5000000000 : ℝ)*x 0 + (1318339149/2500000000 : ℝ)*x 1 + (-544848383/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684330389/5000000000 : ℝ)^2089 ≤ (2741841526229/6250000000000 : ℝ)^1577 := by
    have hnat : (2684330389 : ℕ)^2089*6250000000000^1577 ≤ 2741841526229^1577*5000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684330389 5000000000 2741841526229 6250000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318339149/2500000000 : ℝ)^2089 ≤ (42840840329853/100000000000000 : ℝ)^1577 := by
    have hnat : (1318339149 : ℕ)^2089*100000000000000^1577 ≤ 42840840329853^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318339149 2500000000 42840840329853 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544848383/2500000000 : ℝ)^2089 ≤ (13289695230189/100000000000000 : ℝ)^1577 := by
    have hnat : (544848383 : ℕ)^2089*100000000000000^1577 ≤ 13289695230189^1577*2500000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544848383 2500000000 13289695230189 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684330389/5000000000 : ℝ), (1318339149/2500000000 : ℝ), (-544848383/2500000000 : ℝ)] ![(2741841526229/6250000000000 : ℝ), (42840840329853/100000000000000 : ℝ), (13289695230189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684330389/5000000000 : ℝ)|^2089 ≤ (2741841526229/6250000000000 : ℝ)^1577
        have hw : |(2684330389/5000000000 : ℝ)|=(2684330389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318339149/2500000000 : ℝ)|^2089 ≤ (42840840329853/100000000000000 : ℝ)^1577
        have hw : |(1318339149/2500000000 : ℝ)|=(1318339149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544848383/2500000000 : ℝ)|^2089 ≤ (13289695230189/100000000000000 : ℝ)^1577
        have hw : |(-544848383/2500000000 : ℝ)|=(544848383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1163_box_15 (p : ℝ) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4235514323/10000000000 : ℝ)*x 0 + (553347679/1250000000 : ℝ)*x 1 + (4426781681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235514323/10000000000 : ℝ)^2089 ≤ (8011519065689/25000000000000 : ℝ)^1577 := by
    have hnat : (4235514323 : ℕ)^2089*25000000000000^1577 ≤ 8011519065689^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235514323 10000000000 8011519065689 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553347679/1250000000 : ℝ)^2089 ≤ (33976960598481/100000000000000 : ℝ)^1577 := by
    have hnat : (553347679 : ℕ)^2089*100000000000000^1577 ≤ 33976960598481^1577*1250000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553347679 1250000000 33976960598481 100000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426781681/10000000000 : ℝ)^2089 ≤ (8494240782531/25000000000000 : ℝ)^1577 := by
    have hnat : (4426781681 : ℕ)^2089*25000000000000^1577 ≤ 8494240782531^1577*10000000000^2089 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426781681 10000000000 8494240782531 25000000000000 2089 1577 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2089/512 : ℝ)) 2089 1577 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235514323/10000000000 : ℝ), (553347679/1250000000 : ℝ), (4426781681/10000000000 : ℝ)] ![(8011519065689/25000000000000 : ℝ), (33976960598481/100000000000000 : ℝ), (8494240782531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235514323/10000000000 : ℝ)|^2089 ≤ (8011519065689/25000000000000 : ℝ)^1577
        have hw : |(4235514323/10000000000 : ℝ)|=(4235514323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553347679/1250000000 : ℝ)|^2089 ≤ (33976960598481/100000000000000 : ℝ)^1577
        have hw : |(553347679/1250000000 : ℝ)|=(553347679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426781681/10000000000 : ℝ)|^2089 ≤ (8494240782531/25000000000000 : ℝ)^1577
        have hw : |(4426781681/10000000000 : ℝ)|=(4426781681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1163_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31117/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11863/20000 : ℝ) ∧ (2496/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83171/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11381/100000 : ℝ) ^ (8355/2048 : ℝ) ≤ (441014899748799/3125000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^8355 ≤ (441014899748799/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11381 : ℕ)^8355*3125000000000000000^2048 ≤ 441014899748799^2048*100000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 441014899748799 3125000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (441014899748799/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (703/5000 : ℝ) ^ (8355/2048 : ℝ) ≤ (33429475874101761/100000000000000000000 : ℝ) := by
    have hpowers : (703/5000 : ℝ)^8355 ≤ (33429475874101761/100000000000000000000 : ℝ)^2048 := by
      have hnat : (703 : ℕ)^8355*100000000000000000000^2048 ≤ 33429475874101761^2048*5000^8355 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 5000 33429475874101761 100000000000000000000 8355 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/5000 : ℝ)) (X := (33429475874101761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562941014899748799/1562500000000000000 : ℝ) ≤ (10000691783936711/10000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (1562941014899748799/1562500000000000000 : ℝ)^2048 ≤ (10000691783936711/10000000000000000 : ℝ)^8355 := by
      have hnat : (1562941014899748799 : ℕ)^2048*10000000000000000^8355 ≤ 10000691783936711^8355*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562941014899748799 1562500000000000000 10000691783936711 10000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000691783936711/10000000000000000 : ℝ)) (X := (1562941014899748799/1562500000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047541952666063329/100000000000000000000 : ℝ) ≤ (5000582576016819/5000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (100047541952666063329/100000000000000000000 : ℝ)^2048 ≤ (5000582576016819/5000000000000000 : ℝ)^8355 := by
      have hnat : (100047541952666063329 : ℕ)^2048*5000000000000000^8355 ≤ 5000582576016819^8355*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047541952666063329 100000000000000000000 5000582576016819 5000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000582576016819/5000000000000000 : ℝ)) (X := (100047541952666063329/100000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033429475874101761/50000000000000000000 : ℝ) ≤ (2000327704026113/2000000000000000 : ℝ) ^ (8355/2048 : ℝ) := by
    have hpowers : (50033429475874101761/50000000000000000000 : ℝ)^2048 ≤ (2000327704026113/2000000000000000 : ℝ)^8355 := by
      have hnat : (50033429475874101761 : ℕ)^2048*2000000000000000^8355 ≤ 2000327704026113^8355*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033429475874101761 50000000000000000000 2000327704026113 2000000000000000 2048 8355 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000327704026113/2000000000000000 : ℝ)) (X := (50033429475874101761/50000000000000000000 : ℝ)) (by norm_num) 8355 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(441014899748799/3125000000000000000 : ℝ) ≤ ((281906089310991541/282000000000000000 : ℝ)+2*(473368096927/267900000000000 : ℝ)*(11381/100000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (281906089310991541/282000000000000000 : ℝ)+2*(473368096927/267900000000000 : ℝ)*(11381/100000 : ℝ)=(10000691783936711/10000000000000000 : ℝ) by norm_num, show 1+2*(441014899748799/3125000000000000000 : ℝ)=(1562941014899748799/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33429475874101761/100000000000000000000 : ℝ)+(441014899748799/3125000000000000000 : ℝ) ≤ ((281906089310991541/282000000000000000 : ℝ)+(473368096927/267900000000000 : ℝ)*((703/5000 : ℝ)+(11381/100000 : ℝ)))^(8355/2048 : ℝ) := by
    rw [show (281906089310991541/282000000000000000 : ℝ)+(473368096927/267900000000000 : ℝ)*((703/5000 : ℝ)+(11381/100000 : ℝ))=(5000582576016819/5000000000000000 : ℝ) by norm_num, show 1+(33429475874101761/100000000000000000000 : ℝ)+(441014899748799/3125000000000000000 : ℝ)=(100047541952666063329/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33429475874101761/100000000000000000000 : ℝ) ≤ ((281906089310991541/282000000000000000 : ℝ)+2*(473368096927/267900000000000 : ℝ)*(703/5000 : ℝ))^(8355/2048 : ℝ) := by
    rw [show (281906089310991541/282000000000000000 : ℝ)+2*(473368096927/267900000000000 : ℝ)*(703/5000 : ℝ)=(2000327704026113/2000000000000000 : ℝ) by norm_num, show 1+2*(33429475874101761/100000000000000000000 : ℝ)=(50033429475874101761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (281906089310991541/282000000000000000 : ℝ)*(X 1 0+X 2 0)+(473368096927/267900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (281906089310991541/282000000000000000 : ℝ)) (alpha := (473368096927/267900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (281906089310991541/282000000000000000 : ℝ)*(X 0 1+X 2 1)+(473368096927/267900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (281906089310991541/282000000000000000 : ℝ)) (alpha := (473368096927/267900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (281906089310991541/282000000000000000 : ℝ)*(X 0 2+X 1 2)+(473368096927/267900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8355/2048 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (281906089310991541/282000000000000000 : ℝ)) (alpha := (473368096927/267900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-203068663/1000000000 : ℝ)*X 0 0+(5376006839/10000000000 : ℝ)*X 0 1+(2688003287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324044031/2500000000 : ℝ)*X 1 0+(-85560153/400000000 : ℝ)*X 1 1+(5376005681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1324044289/2500000000 : ℝ)*X 2 0+(672000659/1250000000 : ℝ)*X 2 1+(-133687687/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2234521321/5000000000 : ℝ)*X 0 0+(215508023/500000000 : ℝ)*X 0 1+(4310160339/10000000000 : ℝ)*X 0 2+(2234521321/5000000000 : ℝ)*X 1 0+(215508023/500000000 : ℝ)*X 1 1+(4310160339/10000000000 : ℝ)*X 1 2+(2234521321/5000000000 : ℝ)*X 2 0+(215508023/500000000 : ℝ)*X 2 1+(4310160339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2284473637/10000000000 : ℝ)*X 0 0+(528140399/1000000000 : ℝ)*X 0 1+(5281403987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362980267/10000000000 : ℝ)*X 1 0+(-2176279761/10000000000 : ℝ)*X 1 1+(1320350979/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362980097/10000000000 : ℝ)*X 2 0+(264070199/500000000 : ℝ)*X 2 1+(-68008747/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127018133/5000000000 : ℝ)*X 0 0+(552205371/1250000000 : ℝ)*X 0 1+(4417642833/10000000000 : ℝ)*X 0 2+(2127018133/5000000000 : ℝ)*X 1 0+(552205371/1250000000 : ℝ)*X 1 1+(4417642833/10000000000 : ℝ)*X 1 2+(2127018133/5000000000 : ℝ)*X 2 0+(552205371/1250000000 : ℝ)*X 2 1+(4417642833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-11156897/50000000 : ℝ)*X 0 0+(5217024667/10000000000 : ℝ)*X 0 1+(5385616279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644693107/5000000000 : ℝ)*X 1 0+(-2135149063/10000000000 : ℝ)*X 1 1+(269280779/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289385741/10000000000 : ℝ)*X 2 0+(168300491/312500000 : ℝ)*X 2 1+(-26689369/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((112265313/250000000 : ℝ)*X 0 0+(429923477/1000000000 : ℝ)*X 0 1+(171969403/400000000 : ℝ)*X 0 2+(112265313/250000000 : ℝ)*X 1 0+(429923477/1000000000 : ℝ)*X 1 1+(171969403/400000000 : ℝ)*X 1 2+(112265313/250000000 : ℝ)*X 2 0+(429923477/1000000000 : ℝ)*X 2 1+(171969403/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2084088339/10000000000 : ℝ)*X 0 0+(5439122501/10000000000 : ℝ)*X 0 1+(2636678263/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671082633/1250000000 : ℝ)*X 1 0+(-1089696651/5000000000 : ℝ)*X 1 1+(5273356481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684330389/5000000000 : ℝ)*X 2 0+(1318339149/2500000000 : ℝ)*X 2 1+(-544848383/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4235514323/10000000000 : ℝ)*X 0 0+(553347679/1250000000 : ℝ)*X 0 1+(4426781681/10000000000 : ℝ)*X 0 2+(4235514323/10000000000 : ℝ)*X 1 0+(553347679/1250000000 : ℝ)*X 1 1+(4426781681/10000000000 : ℝ)*X 1 2+(4235514323/10000000000 : ℝ)*X 2 0+(553347679/1250000000 : ℝ)*X 2 1+(4426781681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1163_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31117/50000 : ℝ) ≤ (-2924865501567064246126732605753/4700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1991551/2500000000000 : ℝ)*(upper1) + (37531623/100000000000000 : ℝ)*(upper2) + (10390349/50000000000000 : ℝ)*(upper3) + (70925863/100000000000000 : ℝ)*(lower4) + (3938122015121067/100000000000000 : ℝ)*(major0) + (3938122015121067/100000000000000 : ℝ)*(major1) + (3938122015121067/100000000000000 : ℝ)*(major2) + (139256401/25000000000000 : ℝ)*(sp2) + (113261683/6250000000000 : ℝ)*(sp3) + (2634767167123597/50000000000000 : ℝ)*(sp4) + (5269507657853793/100000000000000 : ℝ)*(sp5) + (5269533777221589/100000000000000 : ℝ)*(sp6) + (2627451610769459/100000000000000 : ℝ)*(sp7) + (26676393401/100000000000000 : ℝ)*(sp13) + (2627453422956387/100000000000000 : ℝ)*(f.failure) + (2634767167123597/50000000000000 : ℝ)*(f.sum) + (19804620314923/4465000000000000000000000000 : ℝ)*base65 + (1232111638389809769/178600000000000000000000000000000 : ℝ)*base68 + (8068037919658809769/178600000000000000000000000000000 : ℝ)*base70 + (7450363544711609769/178600000000000000000000000000000 : ℝ)*base72 + (8677596899/2232500000000000000000000000 : ℝ)*base73 + (2587332239868590231/178600000000000000000000000000000 : ℝ)*base75 + (11543340147075190231/178600000000000000000000000000000 : ℝ)*base77 + (16132192802609769/178600000000000000000000000000000 : ℝ)*base80 + (27520861066943/1116250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (33160683/10000000000000000000000 : ℝ)*base89 + (33160683/10000000000000000000000 : ℝ)*base91 + (33160683/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11863/20000 : ℝ) ≤ (52970311843554274862119812378639/89300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100372387/20000000000000 : ℝ)*(lower1) + (89725067/20000000000000 : ℝ)*(lower2) + (85894161/20000000000000 : ℝ)*(lower3) + (377225803/100000000000000 : ℝ)*(upper4) + (169599103/25000000000000 : ℝ)*(lower5) + (4002618450724159/100000000000000 : ℝ)*(major0) + (4002618450724159/100000000000000 : ℝ)*(major1) + (4002618450724159/100000000000000 : ℝ)*(major2) + (2657490022885493/50000000000000 : ℝ)*(sp0) + (41518834542357/781250000000 : ℝ)*(sp1) + (5314819323720867/100000000000000 : ℝ)*(sp2) + (133524221808809/5000000000000 : ℝ)*(sp3) + (56922434929/10000000000000 : ℝ)*(sp9) + (160722050119/100000000000000 : ℝ)*(sp10) + (133524221808809/5000000000000 : ℝ)*(f.failure) + (2657490022885493/50000000000000 : ℝ)*(f.sum) + (76132659780707/13395000000000000000000000000 : ℝ)*base66 + (527316091716033787/178600000000000000000000000000000 : ℝ)*base67 + (234667323618033787/178600000000000000000000000000000 : ℝ)*base69 + (4013940671334033787/178600000000000000000000000000000 : ℝ)*base71 + (10324229660957/13395000000000000000000000000 : ℝ)*base74 + (4077474510845166213/178600000000000000000000000000000 : ℝ)*base76 + (6386750069567833787/178600000000000000000000000000000 : ℝ)*base77 + (834063711706766213/178600000000000000000000000000000 : ℝ)*base80 + (146260142168627/13395000000000000000000000000 : ℝ)*base82 + (5911681/500000000000000000000 : ℝ)*base89 + (5911681/500000000000000000000 : ℝ)*base91 + (5911681/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2496/3125 : ℝ) ≤ (35664085542958284414294564002379/44650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286810767/100000000000000 : ℝ)*(upper0) + (10243619/5000000000000 : ℝ)*(upper1) + (280559463/100000000000000 : ℝ)*(upper2) + (131021607/50000000000000 : ℝ)*(lower5) + (2235160834791099/50000000000000 : ℝ)*(major0) + (2235160834791099/50000000000000 : ℝ)*(major1) + (2235160834791099/50000000000000 : ℝ)*(major2) + (4216093083/6250000000000 : ℝ)*(sp3) + (9214295109/50000000000000 : ℝ)*(sp4) + (2965734850574241/50000000000000 : ℝ)*(sp8) + (741436213195623/12500000000000 : ℝ)*(sp9) + (741436213195623/12500000000000 : ℝ)*(sp10) + (149123062611291/5000000000000 : ℝ)*(sp11) + (315165257/20000000000000 : ℝ)*(sp12) + (745632177428787/25000000000000 : ℝ)*(f.failure) + (741436213195623/12500000000000 : ℝ)*(f.sum) + (18675203742007/4465000000000000000000000000 : ℝ)*base65 + (882976927782620793/89300000000000000000000000000000 : ℝ)*base68 + (113780292705720793/89300000000000000000000000000000 : ℝ)*base70 + (752099359268479207/89300000000000000000000000000000 : ℝ)*base71 + (3968713390369/2232500000000000000000000000 : ℝ)*base74 + (1235004481370479207/89300000000000000000000000000000 : ℝ)*base75 + (817488161946079207/89300000000000000000000000000000 : ℝ)*base77 + (812569806563679207/89300000000000000000000000000000 : ℝ)*base79 + (9137247683301/2232500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (13947717/2500000000000000000000 : ℝ)*base90 + (13947717/2500000000000000000000 : ℝ)*base92 + (13947717/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83171/100000 : ℝ) ≤ (-74269782220396804639099607356791/89300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34201271/50000000000000 : ℝ)*(upper3) + (49308327/25000000000000 : ℝ)*(lower4) + (18030413/100000000000000 : ℝ)*(upper5) + (4505432002413671/100000000000000 : ℝ)*(major0) + (4505432002413671/100000000000000 : ℝ)*(major1) + (4505432002413671/100000000000000 : ℝ)*(major2) + (22763848047/100000000000000 : ℝ)*(sp4) + (141496649219/100000000000000 : ℝ)*(sp5) + (184980240669/100000000000000 : ℝ)*(sp6) + (266121060353/100000000000000 : ℝ)*(sp7) + (6032610415955219/100000000000000 : ℝ)*(sp12) + (6032491683154047/100000000000000 : ℝ)*(sp13) + (6032448199562597/100000000000000 : ℝ)*(sp14) + (3005687653654047/100000000000000 : ℝ)*(sp15) + (3757442218393/125000000000 : ℝ)*(f.failure) + (3016316589901633/50000000000000 : ℝ)*(f.sum) + (1239628189267/209296875000000000000000000 : ℝ)*base66 + (1300016808769625597/178600000000000000000000000000000 : ℝ)*base68 + (503826691805174403/178600000000000000000000000000000 : ℝ)*base69 + (2158899083485425597/178600000000000000000000000000000 : ℝ)*base72 + (679516473611/104648437500000000000000000 : ℝ)*base74 + (1423902875444374403/178600000000000000000000000000000 : ℝ)*base75 + (806146584496225597/178600000000000000000000000000000 : ℝ)*base78 + (1580153084653425597/178600000000000000000000000000000 : ℝ)*base80 + (35403628396003/13395000000000000000000000000 : ℝ)*base82 + (145337/12500000000000000000 : ℝ)*base89 + (145337/12500000000000000000 : ℝ)*base91 + (145337/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1163_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11863/20000 : ℝ) else (2496/3125 : ℝ) ≤ X j i ∧ X j i ≤ (83171/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1163_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1163_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11863/20000 : ℝ) else (2496/3125 : ℝ) ≤ X j i ∧ X j i ≤ (83171/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1163_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1163_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8355/2048 : ℝ) ≤ p) (hpb : p ≤ (2089/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149883609/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11863/20000 : ℝ) else (2496/3125 : ℝ) ≤ X j i ∧ X j i ≤ (83171/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1163_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
