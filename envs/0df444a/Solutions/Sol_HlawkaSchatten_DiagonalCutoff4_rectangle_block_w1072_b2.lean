-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1072_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:11:30.763987+00:00
-- url     : https://prove2.me/submissions/15c8eba3-9af6-4d24-8971-cbbc8a596000

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
theorem support_rectangle_w1072_s6_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200769049/10000000000 : ℝ)*x 0 + (1348699259/2500000000 : ℝ)*x 1 + (1052809907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200769049/10000000000 : ℝ)^8265 ≤ (13366133336629/100000000000000 : ℝ)^6217 := by
    have hnat : (2200769049 : ℕ)^8265*100000000000000^6217 ≤ 13366133336629^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200769049 10000000000 13366133336629 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348699259/2500000000 : ℝ)^8265 ≤ (11005823358621/25000000000000 : ℝ)^6217 := by
    have hnat : (1348699259 : ℕ)^8265*25000000000000^6217 ≤ 11005823358621^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348699259 2500000000 11005823358621 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052809907/2000000000 : ℝ)^8265 ≤ (21305286609347/50000000000000 : ℝ)^6217 := by
    have hnat : (1052809907 : ℕ)^8265*50000000000000^6217 ≤ 21305286609347^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052809907 2000000000 21305286609347 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200769049/10000000000 : ℝ), (1348699259/2500000000 : ℝ), (1052809907/2000000000 : ℝ)] ![(13366133336629/100000000000000 : ℝ), (11005823358621/25000000000000 : ℝ), (21305286609347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200769049/10000000000 : ℝ)|^8265 ≤ (13366133336629/100000000000000 : ℝ)^6217
        have hw : |(-2200769049/10000000000 : ℝ)|=(2200769049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348699259/2500000000 : ℝ)|^8265 ≤ (11005823358621/25000000000000 : ℝ)^6217
        have hw : |(1348699259/2500000000 : ℝ)|=(1348699259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052809907/2000000000 : ℝ)|^8265 ≤ (21305286609347/50000000000000 : ℝ)^6217
        have hw : |(1052809907/2000000000 : ℝ)|=(1052809907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345101627/10000000000 : ℝ)*x 0 + (-226711173/1000000000 : ℝ)*x 1 + (2632024871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345101627/10000000000 : ℝ)^8265 ≤ (21742496409387/50000000000000 : ℝ)^6217 := by
    have hnat : (5345101627 : ℕ)^8265*50000000000000^6217 ≤ 21742496409387^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345101627 10000000000 21742496409387 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226711173/1000000000 : ℝ)^8265 ≤ (2780886344187/20000000000000 : ℝ)^6217 := by
    have hnat : (226711173 : ℕ)^8265*20000000000000^6217 ≤ 2780886344187^6217*1000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226711173 1000000000 2780886344187 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632024871/5000000000 : ℝ)^8265 ≤ (8522115089251/20000000000000 : ℝ)^6217 := by
    have hnat : (2632024871 : ℕ)^8265*20000000000000^6217 ≤ 8522115089251^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632024871 5000000000 8522115089251 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345101627/10000000000 : ℝ), (-226711173/1000000000 : ℝ), (2632024871/5000000000 : ℝ)] ![(21742496409387/50000000000000 : ℝ), (2780886344187/20000000000000 : ℝ), (8522115089251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345101627/10000000000 : ℝ)|^8265 ≤ (21742496409387/50000000000000 : ℝ)^6217
        have hw : |(5345101627/10000000000 : ℝ)|=(5345101627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226711173/1000000000 : ℝ)|^8265 ≤ (2780886344187/20000000000000 : ℝ)^6217
        have hw : |(-226711173/1000000000 : ℝ)|=(226711173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632024871/5000000000 : ℝ)|^8265 ≤ (8522115089251/20000000000000 : ℝ)^6217
        have hw : |(2632024871/5000000000 : ℝ)|=(2632024871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345100831/10000000000 : ℝ)*x 0 + (5264050179/10000000000 : ℝ)*x 1 + (-2267112209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345100831/10000000000 : ℝ)^8265 ≤ (43484984209659/100000000000000 : ℝ)^6217 := by
    have hnat : (5345100831 : ℕ)^8265*100000000000000^6217 ≤ 43484984209659^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345100831 10000000000 43484984209659 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264050179/10000000000 : ℝ)^8265 ≤ (21305290074443/50000000000000 : ℝ)^6217 := by
    have hnat : (5264050179 : ℕ)^8265*50000000000000^6217 ≤ 21305290074443^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264050179 10000000000 21305290074443 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267112209/10000000000 : ℝ)^8265 ≤ (2780887125289/20000000000000 : ℝ)^6217 := by
    have hnat : (2267112209 : ℕ)^8265*20000000000000^6217 ≤ 2780887125289^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267112209 10000000000 2780887125289 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345100831/10000000000 : ℝ), (5264050179/10000000000 : ℝ), (-2267112209/10000000000 : ℝ)] ![(43484984209659/100000000000000 : ℝ), (21305290074443/50000000000000 : ℝ), (2780887125289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345100831/10000000000 : ℝ)|^8265 ≤ (43484984209659/100000000000000 : ℝ)^6217
        have hw : |(5345100831/10000000000 : ℝ)|=(5345100831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264050179/10000000000 : ℝ)|^8265 ≤ (21305290074443/50000000000000 : ℝ)^6217
        have hw : |(5264050179/10000000000 : ℝ)|=(5264050179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2267112209/10000000000 : ℝ)|^8265 ≤ (2780887125289/20000000000000 : ℝ)^6217
        have hw : |(-2267112209/10000000000 : ℝ)|=(2267112209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093650743/2500000000 : ℝ)*x 0 + (4248229327/10000000000 : ℝ)*x 1 + (4504781721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093650743/2500000000 : ℝ)^8265 ≤ (33316309718941/100000000000000 : ℝ)^6217 := by
    have hnat : (1093650743 : ℕ)^8265*100000000000000^6217 ≤ 33316309718941^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093650743 2500000000 33316309718941 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248229327/10000000000 : ℝ)^8265 ≤ (6408589586031/20000000000000 : ℝ)^6217 := by
    have hnat : (4248229327 : ℕ)^8265*20000000000000^6217 ≤ 6408589586031^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248229327 10000000000 6408589586031 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504781721/10000000000 : ℝ)^8265 ≤ (346407423329/1000000000000 : ℝ)^6217 := by
    have hnat : (4504781721 : ℕ)^8265*1000000000000^6217 ≤ 346407423329^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504781721 10000000000 346407423329 1000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093650743/2500000000 : ℝ), (4248229327/10000000000 : ℝ), (4504781721/10000000000 : ℝ)] ![(33316309718941/100000000000000 : ℝ), (6408589586031/20000000000000 : ℝ), (346407423329/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093650743/2500000000 : ℝ)|^8265 ≤ (33316309718941/100000000000000 : ℝ)^6217
        have hw : |(1093650743/2500000000 : ℝ)|=(1093650743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248229327/10000000000 : ℝ)|^8265 ≤ (6408589586031/20000000000000 : ℝ)^6217
        have hw : |(4248229327/10000000000 : ℝ)|=(4248229327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504781721/10000000000 : ℝ)|^8265 ≤ (346407423329/1000000000000 : ℝ)^6217
        have hw : |(4504781721/10000000000 : ℝ)|=(4504781721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17606193/80000000 : ℝ)*x 0 + (82255937/156250000 : ℝ)*x 1 + (2697232739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17606193/80000000 : ℝ)^8265 ≤ (133661743207/1000000000000 : ℝ)^6217 := by
    have hnat : (17606193 : ℕ)^8265*1000000000000^6217 ≤ 133661743207^6217*80000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17606193 80000000 133661743207 1000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82255937/156250000 : ℝ)^8265 ≤ (42614129100387/100000000000000 : ℝ)^6217 := by
    have hnat : (82255937 : ℕ)^8265*100000000000000^6217 ≤ 42614129100387^6217*156250000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82255937 156250000 42614129100387 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697232739/5000000000 : ℝ)^8265 ≤ (44019696566281/100000000000000 : ℝ)^6217 := by
    have hnat : (2697232739 : ℕ)^8265*100000000000000^6217 ≤ 44019696566281^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697232739 5000000000 44019696566281 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17606193/80000000 : ℝ), (82255937/156250000 : ℝ), (2697232739/5000000000 : ℝ)] ![(133661743207/1000000000000 : ℝ), (42614129100387/100000000000000 : ℝ), (44019696566281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17606193/80000000 : ℝ)|^8265 ≤ (133661743207/1000000000000 : ℝ)^6217
        have hw : |(-17606193/80000000 : ℝ)|=(17606193/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82255937/156250000 : ℝ)|^8265 ≤ (42614129100387/100000000000000 : ℝ)^6217
        have hw : |(82255937/156250000 : ℝ)|=(82255937/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697232739/5000000000 : ℝ)|^8265 ≤ (44019696566281/100000000000000 : ℝ)^6217
        have hw : |(2697232739/5000000000 : ℝ)|=(2697232739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312153143/10000000000 : ℝ)*x 0 + (-2136696229/10000000000 : ℝ)*x 1 + (5394465533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312153143/10000000000 : ℝ)^8265 ≤ (8625800352667/20000000000000 : ℝ)^6217 := by
    have hnat : (5312153143 : ℕ)^8265*20000000000000^6217 ≤ 8625800352667^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312153143 10000000000 8625800352667 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136696229/10000000000 : ℝ)^8265 ≤ (12851301058561/100000000000000 : ℝ)^6217 := by
    have hnat : (2136696229 : ℕ)^8265*100000000000000^6217 ≤ 12851301058561^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136696229 10000000000 12851301058561 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394465533/10000000000 : ℝ)^8265 ≤ (5502462145367/12500000000000 : ℝ)^6217 := by
    have hnat : (5394465533 : ℕ)^8265*12500000000000^6217 ≤ 5502462145367^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394465533 10000000000 5502462145367 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312153143/10000000000 : ℝ), (-2136696229/10000000000 : ℝ), (5394465533/10000000000 : ℝ)] ![(8625800352667/20000000000000 : ℝ), (12851301058561/100000000000000 : ℝ), (5502462145367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312153143/10000000000 : ℝ)|^8265 ≤ (8625800352667/20000000000000 : ℝ)^6217
        have hw : |(5312153143/10000000000 : ℝ)|=(5312153143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136696229/10000000000 : ℝ)|^8265 ≤ (12851301058561/100000000000000 : ℝ)^6217
        have hw : |(-2136696229/10000000000 : ℝ)|=(2136696229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394465533/10000000000 : ℝ)|^8265 ≤ (5502462145367/12500000000000 : ℝ)^6217
        have hw : |(5394465533/10000000000 : ℝ)|=(5394465533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328038213/2500000000 : ℝ)*x 0 + (5394465911/10000000000 : ℝ)*x 1 + (-2136696109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328038213/2500000000 : ℝ)^8265 ≤ (21564499311219/50000000000000 : ℝ)^6217 := by
    have hnat : (1328038213 : ℕ)^8265*50000000000000^6217 ≤ 21564499311219^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328038213 2500000000 21564499311219 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394465911/10000000000 : ℝ)^8265 ≤ (44019701263583/100000000000000 : ℝ)^6217 := by
    have hnat : (5394465911 : ℕ)^8265*100000000000000^6217 ≤ 44019701263583^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394465911 10000000000 44019701263583 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136696109/10000000000 : ℝ)^8265 ≤ (2570260019811/20000000000000 : ℝ)^6217 := by
    have hnat : (2136696109 : ℕ)^8265*20000000000000^6217 ≤ 2570260019811^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136696109 10000000000 2570260019811 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328038213/2500000000 : ℝ), (5394465911/10000000000 : ℝ), (-2136696109/10000000000 : ℝ)] ![(21564499311219/50000000000000 : ℝ), (44019701263583/100000000000000 : ℝ), (2570260019811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328038213/2500000000 : ℝ)|^8265 ≤ (21564499311219/50000000000000 : ℝ)^6217
        have hw : |(1328038213/2500000000 : ℝ)|=(1328038213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394465911/10000000000 : ℝ)|^8265 ≤ (44019701263583/100000000000000 : ℝ)^6217
        have hw : |(5394465911/10000000000 : ℝ)|=(5394465911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136696109/10000000000 : ℝ)|^8265 ≤ (2570260019811/20000000000000 : ℝ)^6217
        have hw : |(-2136696109/10000000000 : ℝ)|=(2136696109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s6_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187306569/5000000000 : ℝ)*x 0 + (2252066727/5000000000 : ℝ)*x 1 + (2124439971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187306569/5000000000 : ℝ)^8265 ≤ (2082275790389/6250000000000 : ℝ)^6217 := by
    have hnat : (2187306569 : ℕ)^8265*6250000000000^6217 ≤ 2082275790389^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187306569 5000000000 2082275790389 6250000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252066727/5000000000 : ℝ)^8265 ≤ (4329264412649/12500000000000 : ℝ)^6217 := by
    have hnat : (2252066727 : ℕ)^8265*12500000000000^6217 ≤ 4329264412649^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252066727 5000000000 4329264412649 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124439971/5000000000 : ℝ)^8265 ≤ (16024736021981/50000000000000 : ℝ)^6217 := by
    have hnat : (2124439971 : ℕ)^8265*50000000000000^6217 ≤ 16024736021981^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124439971 5000000000 16024736021981 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187306569/5000000000 : ℝ), (2252066727/5000000000 : ℝ), (2124439971/5000000000 : ℝ)] ![(2082275790389/6250000000000 : ℝ), (4329264412649/12500000000000 : ℝ), (16024736021981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187306569/5000000000 : ℝ)|^8265 ≤ (2082275790389/6250000000000 : ℝ)^6217
        have hw : |(2187306569/5000000000 : ℝ)|=(2187306569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252066727/5000000000 : ℝ)|^8265 ≤ (4329264412649/12500000000000 : ℝ)^6217
        have hw : |(2252066727/5000000000 : ℝ)|=(2252066727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124439971/5000000000 : ℝ)|^8265 ≤ (16024736021981/50000000000000 : ℝ)^6217
        have hw : |(2124439971/5000000000 : ℝ)|=(2124439971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7009/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (1401/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1401/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1401/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1401/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1401/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1401/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1401/12500 : ℝ) ^ (1033/256 : ℝ) ≤ (2922317897154953/20000000000000000000 : ℝ) := by
    have hpowers : (1401/12500 : ℝ)^1033 ≤ (2922317897154953/20000000000000000000 : ℝ)^256 := by
      have hnat : (1401 : ℕ)^1033*20000000000000000000^256 ≤ 2922317897154953^256*12500^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 12500 2922317897154953 20000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/12500 : ℝ)) (X := (2922317897154953/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14061/100000 : ℝ) ^ (1033/256 : ℝ) ≤ (18242412932086239/50000000000000000000 : ℝ) := by
    have hpowers : (14061/100000 : ℝ)^1033 ≤ (18242412932086239/50000000000000000000 : ℝ)^256 := by
      have hnat : (14061 : ℕ)^1033*50000000000000000000^256 ≤ 18242412932086239^256*100000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14061 100000 18242412932086239 50000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14061/100000 : ℝ)) (X := (18242412932086239/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002922317897154953/10000000000000000000 : ℝ) ≤ (10000724134728139/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (10002922317897154953/10000000000000000000 : ℝ)^256 ≤ (10000724134728139/10000000000000000 : ℝ)^1033 := by
      have hnat : (10002922317897154953 : ℕ)^256*10000000000000000^1033 ≤ 10000724134728139^1033*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002922317897154953 10000000000000000000 10000724134728139 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000724134728139/10000000000000000 : ℝ)) (X := (10002922317897154953/10000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051096415349947243/100000000000000000000 : ℝ) ≤ (10001266037695117/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (100051096415349947243/100000000000000000000 : ℝ)^256 ≤ (10001266037695117/10000000000000000 : ℝ)^1033 := by
      have hnat : (100051096415349947243 : ℕ)^256*10000000000000000^1033 ≤ 10001266037695117^1033*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051096415349947243 100000000000000000000 10001266037695117 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001266037695117/10000000000000000 : ℝ)) (X := (100051096415349947243/100000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018242412932086239/25000000000000000000 : ℝ) ≤ (2000361588132419/2000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (25018242412932086239/25000000000000000000 : ℝ)^256 ≤ (2000361588132419/2000000000000000 : ℝ)^1033 := by
      have hnat : (25018242412932086239 : ℕ)^256*2000000000000000^1033 ≤ 2000361588132419^1033*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018242412932086239 25000000000000000000 2000361588132419 2000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000361588132419/2000000000000000 : ℝ)) (X := (25018242412932086239/25000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2922317897154953/20000000000000000000 : ℝ) ≤ ((3168879851052400191/3170000000000000000 : ℝ)+2*(90317161163/47550000000000 : ℝ)*(1401/12500 : ℝ))^(1033/256 : ℝ) := by
    rw [show (3168879851052400191/3170000000000000000 : ℝ)+2*(90317161163/47550000000000 : ℝ)*(1401/12500 : ℝ)=(10000724134728139/10000000000000000 : ℝ) by norm_num, show 1+2*(2922317897154953/20000000000000000000 : ℝ)=(10002922317897154953/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18242412932086239/50000000000000000000 : ℝ)+(2922317897154953/20000000000000000000 : ℝ) ≤ ((3168879851052400191/3170000000000000000 : ℝ)+(90317161163/47550000000000 : ℝ)*((14061/100000 : ℝ)+(1401/12500 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (3168879851052400191/3170000000000000000 : ℝ)+(90317161163/47550000000000 : ℝ)*((14061/100000 : ℝ)+(1401/12500 : ℝ))=(10001266037695117/10000000000000000 : ℝ) by norm_num, show 1+(18242412932086239/50000000000000000000 : ℝ)+(2922317897154953/20000000000000000000 : ℝ)=(100051096415349947243/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18242412932086239/50000000000000000000 : ℝ) ≤ ((3168879851052400191/3170000000000000000 : ℝ)+2*(90317161163/47550000000000 : ℝ)*(14061/100000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (3168879851052400191/3170000000000000000 : ℝ)+2*(90317161163/47550000000000 : ℝ)*(14061/100000 : ℝ)=(2000361588132419/2000000000000000 : ℝ) by norm_num, show 1+2*(18242412932086239/50000000000000000000 : ℝ)=(25018242412932086239/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3168879851052400191/3170000000000000000 : ℝ)*(X 1 0+X 2 0)+(90317161163/47550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (3168879851052400191/3170000000000000000 : ℝ)) (alpha := (90317161163/47550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3168879851052400191/3170000000000000000 : ℝ)*(X 0 1+X 2 1)+(90317161163/47550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (3168879851052400191/3170000000000000000 : ℝ)) (alpha := (90317161163/47550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3168879851052400191/3170000000000000000 : ℝ)*(X 0 2+X 1 2)+(90317161163/47550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (1401/12500 : ℝ)) (hi := (14061/100000 : ℝ)) (c := (3168879851052400191/3170000000000000000 : ℝ)) (alpha := (90317161163/47550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2200769049/10000000000 : ℝ)*X 0 0+(1348699259/2500000000 : ℝ)*X 0 1+(1052809907/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345101627/10000000000 : ℝ)*X 1 0+(-226711173/1000000000 : ℝ)*X 1 1+(2632024871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345100831/10000000000 : ℝ)*X 2 0+(5264050179/10000000000 : ℝ)*X 2 1+(-2267112209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093650743/2500000000 : ℝ)*X 0 0+(4248229327/10000000000 : ℝ)*X 0 1+(4504781721/10000000000 : ℝ)*X 0 2+(1093650743/2500000000 : ℝ)*X 1 0+(4248229327/10000000000 : ℝ)*X 1 1+(4504781721/10000000000 : ℝ)*X 1 2+(1093650743/2500000000 : ℝ)*X 2 0+(4248229327/10000000000 : ℝ)*X 2 1+(4504781721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17606193/80000000 : ℝ)*X 0 0+(82255937/156250000 : ℝ)*X 0 1+(2697232739/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312153143/10000000000 : ℝ)*X 1 0+(-2136696229/10000000000 : ℝ)*X 1 1+(5394465533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328038213/2500000000 : ℝ)*X 2 0+(5394465911/10000000000 : ℝ)*X 2 1+(-2136696109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187306569/5000000000 : ℝ)*X 0 0+(2252066727/5000000000 : ℝ)*X 0 1+(2124439971/5000000000 : ℝ)*X 0 2+(2187306569/5000000000 : ℝ)*X 1 0+(2252066727/5000000000 : ℝ)*X 1 1+(2124439971/5000000000 : ℝ)*X 1 2+(2187306569/5000000000 : ℝ)*X 2 0+(2252066727/5000000000 : ℝ)*X 2 1+(2124439971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (306375797087441236589569371/79250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137964681/10000000000000 : ℝ)*(base19) + (403517609/100000000000000 : ℝ)*(base23) + (141418939/100000000000000 : ℝ)*(upper2) + (22203283/6250000000000 : ℝ)*(upper3) + (5773164681734327/100000000000000 : ℝ)*(major0) + (5773164681734327/100000000000000 : ℝ)*(major1) + (721645585216791/12500000000000 : ℝ)*(major2) + (3824199196540821/50000000000000 : ℝ)*(sp0) + (3824216007028271/50000000000000 : ℝ)*(sp1) + (7648416493073753/100000000000000 : ℝ)*(sp2) + (1948933914196703/50000000000000 : ℝ)*(sp3) + (35000621709/100000000000000 : ℝ)*(sp4) + (16497111989/100000000000000 : ℝ)*(sp6) + (17507817/62500000000 : ℝ)*(sp7) + (1948947920450303/50000000000000 : ℝ)*(f.failure) + (7648433393703351/100000000000000 : ℝ)*(f.sum) + (839535654727/475500000000000000000000000 : ℝ)*base65 + (5752436243718343543/317000000000000000000000000000000 : ℝ)*base68 + (1233042608232196243/118875000000000000000000000000000 : ℝ)*base69 + (1442398074078343543/317000000000000000000000000000000 : ℝ)*base72 + (1705376736649/951000000000000000000000000 : ℝ)*base74 + (878595093791803757/118875000000000000000000000000000 : ℝ)*base76 + (9594908452154630629/951000000000000000000000000000000 : ℝ)*base78 + (6601938108629630629/951000000000000000000000000000000 : ℝ)*base80 + (14682955058431/2377500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (85111219/5000000000000000000000 : ℝ)*base89 + (85111219/5000000000000000000000 : ℝ)*base91 + (35111219/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (738519625604754856604401909/158500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1087508659/100000000000000 : ℝ)*(base19) + (842376153/100000000000000 : ℝ)*(base23) + (13951713/25000000000000 : ℝ)*(upper2) + (103475891/50000000000000 : ℝ)*(upper3) + (103912427/100000000000000 : ℝ)*(upper5) + (5802457432528967/100000000000000 : ℝ)*(major0) + (5802457432528967/100000000000000 : ℝ)*(major1) + (5802457432528967/100000000000000 : ℝ)*(major2) + (5155570563/20000000000000 : ℝ)*(sp1) + (3721254511/10000000000000 : ℝ)*(sp2) + (7687241138986749/100000000000000 : ℝ)*(sp4) + (307488570945011/4000000000000 : ℝ)*(sp5) + (3843601542032743/50000000000000 : ℝ)*(sp6) + (979418392689213/25000000000000 : ℝ)*(sp7) + (979418392689213/25000000000000 : ℝ)*(f.failure) + (7687241138986749/100000000000000 : ℝ)*(f.sum) + (8801665209763/4755000000000000000000000000 : ℝ)*base66 + (5523053526335698091/951000000000000000000000000000000 : ℝ)*base67 + (961380644130301909/951000000000000000000000000000000 : ℝ)*base70 + (6652285706430301909/951000000000000000000000000000000 : ℝ)*base72 + (15438061471423/4755000000000000000000000000 : ℝ)*base74 + (8853016117736698091/951000000000000000000000000000000 : ℝ)*base75 + (3164760666017698091/951000000000000000000000000000000 : ℝ)*base77 + (11603102364131698091/951000000000000000000000000000000 : ℝ)*base79 + (14135669615429/2377500000000000000000000000 : ℝ)*base82 + (21978649/2500000000000000000000 : ℝ)*base89 + (21978649/2500000000000000000000 : ℝ)*base91 + (21978649/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1072_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1072_s7_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220080883/1000000000 : ℝ)*x 0 + (5394342967/10000000000 : ℝ)*x 1 + (1316119357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220080883/1000000000 : ℝ)^8265 ≤ (3341613633189/25000000000000 : ℝ)^6217 := by
    have hnat : (220080883 : ℕ)^8265*25000000000000^6217 ≤ 3341613633189^6217*1000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220080883 1000000000 3341613633189 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394342967/10000000000 : ℝ)^8265 ≤ (11004591884611/25000000000000 : ℝ)^6217 := by
    have hnat : (5394342967 : ℕ)^8265*25000000000000^6217 ≤ 11004591884611^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394342967 10000000000 11004591884611 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316119357/2500000000 : ℝ)^8265 ≤ (10653794477169/25000000000000 : ℝ)^6217 := by
    have hnat : (1316119357 : ℕ)^8265*25000000000000^6217 ≤ 10653794477169^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316119357 2500000000 10653794477169 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220080883/1000000000 : ℝ), (5394342967/10000000000 : ℝ), (1316119357/2500000000 : ℝ)] ![(3341613633189/25000000000000 : ℝ), (11004591884611/25000000000000 : ℝ), (10653794477169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220080883/1000000000 : ℝ)|^8265 ≤ (3341613633189/25000000000000 : ℝ)^6217
        have hw : |(-220080883/1000000000 : ℝ)|=(220080883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394342967/10000000000 : ℝ)|^8265 ≤ (11004591884611/25000000000000 : ℝ)^6217
        have hw : |(5394342967/10000000000 : ℝ)|=(5394342967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316119357/2500000000 : ℝ)|^8265 ≤ (10653794477169/25000000000000 : ℝ)^6217
        have hw : |(1316119357/2500000000 : ℝ)|=(1316119357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334061739/625000000 : ℝ)*x 0 + (-1133348957/5000000000 : ℝ)*x 1 + (2632238821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334061739/625000000 : ℝ)^8265 ≤ (1739350479603/4000000000000 : ℝ)^6217 := by
    have hnat : (334061739 : ℕ)^8265*4000000000000^6217 ≤ 1739350479603^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334061739 625000000 1739350479603 4000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133348957/5000000000 : ℝ)^8265 ≤ (2780211557467/20000000000000 : ℝ)^6217 := by
    have hnat : (1133348957 : ℕ)^8265*20000000000000^6217 ≤ 2780211557467^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133348957 5000000000 2780211557467 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632238821/5000000000 : ℝ)^8265 ≤ (10653795052907/25000000000000 : ℝ)^6217 := by
    have hnat : (2632238821 : ℕ)^8265*25000000000000^6217 ≤ 10653795052907^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632238821 5000000000 10653795052907 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334061739/625000000 : ℝ), (-1133348957/5000000000 : ℝ), (2632238821/5000000000 : ℝ)] ![(1739350479603/4000000000000 : ℝ), (2780211557467/20000000000000 : ℝ), (10653795052907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334061739/625000000 : ℝ)|^8265 ≤ (1739350479603/4000000000000 : ℝ)^6217
        have hw : |(334061739/625000000 : ℝ)|=(334061739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133348957/5000000000 : ℝ)|^8265 ≤ (2780211557467/20000000000000 : ℝ)^6217
        have hw : |(-1133348957/5000000000 : ℝ)|=(1133348957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632238821/5000000000 : ℝ)|^8265 ≤ (10653795052907/25000000000000 : ℝ)^6217
        have hw : |(2632238821/5000000000 : ℝ)|=(2632238821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344987913/10000000000 : ℝ)*x 0 + (5264477469/10000000000 : ℝ)*x 1 + (-90667921/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344987913/10000000000 : ℝ)^8265 ≤ (8696752590529/20000000000000 : ℝ)^6217 := by
    have hnat : (5344987913 : ℕ)^8265*20000000000000^6217 ≤ 8696752590529^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344987913 10000000000 8696752590529 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264477469/10000000000 : ℝ)^8265 ≤ (5326897293737/12500000000000 : ℝ)^6217 := by
    have hnat : (5264477469 : ℕ)^8265*12500000000000^6217 ≤ 5326897293737^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264477469 10000000000 5326897293737 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90667921/400000000 : ℝ)^8265 ≤ (2780211738463/20000000000000 : ℝ)^6217 := by
    have hnat : (90667921 : ℕ)^8265*20000000000000^6217 ≤ 2780211738463^6217*400000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90667921 400000000 2780211738463 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344987913/10000000000 : ℝ), (5264477469/10000000000 : ℝ), (-90667921/400000000 : ℝ)] ![(8696752590529/20000000000000 : ℝ), (5326897293737/12500000000000 : ℝ), (2780211738463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344987913/10000000000 : ℝ)|^8265 ≤ (8696752590529/20000000000000 : ℝ)^6217
        have hw : |(5344987913/10000000000 : ℝ)|=(5344987913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264477469/10000000000 : ℝ)|^8265 ≤ (5326897293737/12500000000000 : ℝ)^6217
        have hw : |(5264477469/10000000000 : ℝ)|=(5264477469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90667921/400000000 : ℝ)|^8265 ≤ (2780211738463/20000000000000 : ℝ)^6217
        have hw : |(-90667921/400000000 : ℝ)|=(90667921/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374625541/10000000000 : ℝ)*x 0 + (4249092031/10000000000 : ℝ)*x 1 + (2251956557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374625541/10000000000 : ℝ)^8265 ≤ (8329134555619/25000000000000 : ℝ)^6217 := by
    have hnat : (4374625541 : ℕ)^8265*25000000000000^6217 ≤ 8329134555619^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374625541 10000000000 8329134555619 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249092031/10000000000 : ℝ)^8265 ≤ (1282063954439/4000000000000 : ℝ)^6217 := by
    have hnat : (4249092031 : ℕ)^8265*4000000000000^6217 ≤ 1282063954439^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249092031 10000000000 1282063954439 4000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251956557/5000000000 : ℝ)^8265 ≤ (8657965726379/25000000000000 : ℝ)^6217 := by
    have hnat : (2251956557 : ℕ)^8265*25000000000000^6217 ≤ 8657965726379^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251956557 5000000000 8657965726379 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374625541/10000000000 : ℝ), (4249092031/10000000000 : ℝ), (2251956557/5000000000 : ℝ)] ![(8329134555619/25000000000000 : ℝ), (1282063954439/4000000000000 : ℝ), (8657965726379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374625541/10000000000 : ℝ)|^8265 ≤ (8329134555619/25000000000000 : ℝ)^6217
        have hw : |(4374625541/10000000000 : ℝ)|=(4374625541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249092031/10000000000 : ℝ)|^8265 ≤ (1282063954439/4000000000000 : ℝ)^6217
        have hw : |(4249092031/10000000000 : ℝ)|=(4249092031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251956557/5000000000 : ℝ)|^8265 ≤ (8657965726379/25000000000000 : ℝ)^6217
        have hw : |(2251956557/5000000000 : ℝ)|=(2251956557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200813797/10000000000 : ℝ)*x 0 + (105296067/200000000 : ℝ)*x 1 + (1348503987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200813797/10000000000 : ℝ)^8265 ≤ (13366494636989/100000000000000 : ℝ)^6217 := by
    have hnat : (2200813797 : ℕ)^8265*100000000000000^6217 ≤ 13366494636989^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200813797 10000000000 13366494636989 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105296067/200000000 : ℝ)^8265 ≤ (5327335667457/12500000000000 : ℝ)^6217 := by
    have hnat : (105296067 : ℕ)^8265*12500000000000^6217 ≤ 5327335667457^6217*200000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105296067 200000000 5327335667457 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348503987/2500000000 : ℝ)^8265 ≤ (44014820008929/100000000000000 : ℝ)^6217 := by
    have hnat : (1348503987 : ℕ)^8265*100000000000000^6217 ≤ 44014820008929^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348503987 2500000000 44014820008929 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200813797/10000000000 : ℝ), (105296067/200000000 : ℝ), (1348503987/2500000000 : ℝ)] ![(13366494636989/100000000000000 : ℝ), (5327335667457/12500000000000 : ℝ), (44014820008929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200813797/10000000000 : ℝ)|^8265 ≤ (13366494636989/100000000000000 : ℝ)^6217
        have hw : |(-2200813797/10000000000 : ℝ)|=(2200813797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105296067/200000000 : ℝ)|^8265 ≤ (5327335667457/12500000000000 : ℝ)^6217
        have hw : |(105296067/200000000 : ℝ)|=(105296067/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348503987/2500000000 : ℝ)|^8265 ≤ (44014820008929/100000000000000 : ℝ)^6217
        have hw : |(1348503987/2500000000 : ℝ)|=(1348503987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332016357/625000000 : ℝ)*x 0 + (-33393119/156250000 : ℝ)*x 1 + (1348503987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332016357/625000000 : ℝ)^8265 ≤ (43130173602773/100000000000000 : ℝ)^6217 := by
    have hnat : (332016357 : ℕ)^8265*100000000000000^6217 ≤ 43130173602773^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332016357 625000000 43130173602773 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33393119/156250000 : ℝ)^8265 ≤ (12855006378067/100000000000000 : ℝ)^6217 := by
    have hnat : (33393119 : ℕ)^8265*100000000000000^6217 ≤ 12855006378067^6217*156250000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33393119 156250000 12855006378067 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348503987/2500000000 : ℝ)^8265 ≤ (44014820008929/100000000000000 : ℝ)^6217 := by
    have hnat : (1348503987 : ℕ)^8265*100000000000000^6217 ≤ 44014820008929^6217*2500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348503987 2500000000 44014820008929 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332016357/625000000 : ℝ), (-33393119/156250000 : ℝ), (1348503987/2500000000 : ℝ)] ![(43130173602773/100000000000000 : ℝ), (12855006378067/100000000000000 : ℝ), (44014820008929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332016357/625000000 : ℝ)|^8265 ≤ (43130173602773/100000000000000 : ℝ)^6217
        have hw : |(332016357/625000000 : ℝ)|=(332016357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33393119/156250000 : ℝ)|^8265 ≤ (12855006378067/100000000000000 : ℝ)^6217
        have hw : |(-33393119/156250000 : ℝ)|=(33393119/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348503987/2500000000 : ℝ)|^8265 ≤ (44014820008929/100000000000000 : ℝ)^6217
        have hw : |(1348503987/2500000000 : ℝ)|=(1348503987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312261713/10000000000 : ℝ)*x 0 + (5394015947/10000000000 : ℝ)*x 1 + (-427431923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312261713/10000000000 : ℝ)^8265 ≤ (21565086806783/50000000000000 : ℝ)^6217 := by
    have hnat : (5312261713 : ℕ)^8265*50000000000000^6217 ≤ 21565086806783^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312261713 10000000000 21565086806783 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394015947/10000000000 : ℝ)^8265 ≤ (44014819998081/100000000000000 : ℝ)^6217 := by
    have hnat : (5394015947 : ℕ)^8265*100000000000000^6217 ≤ 44014819998081^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394015947 10000000000 44014819998081 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427431923/2000000000 : ℝ)^8265 ≤ (1285500637007/10000000000000 : ℝ)^6217 := by
    have hnat : (427431923 : ℕ)^8265*10000000000000^6217 ≤ 1285500637007^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427431923 2000000000 1285500637007 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312261713/10000000000 : ℝ), (5394015947/10000000000 : ℝ), (-427431923/2000000000 : ℝ)] ![(21565086806783/50000000000000 : ℝ), (44014819998081/100000000000000 : ℝ), (1285500637007/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312261713/10000000000 : ℝ)|^8265 ≤ (21565086806783/50000000000000 : ℝ)^6217
        have hw : |(5312261713/10000000000 : ℝ)|=(5312261713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394015947/10000000000 : ℝ)|^8265 ≤ (44014819998081/100000000000000 : ℝ)^6217
        have hw : |(5394015947/10000000000 : ℝ)|=(5394015947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427431923/2000000000 : ℝ)|^8265 ≤ (1285500637007/10000000000000 : ℝ)^6217
        have hw : |(-427431923/2000000000 : ℝ)|=(427431923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s7_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136707359/312500000 : ℝ)*x 0 + (4503273913/10000000000 : ℝ)*x 1 + (212486677/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136707359/312500000 : ℝ)^8265 ≤ (33316638932629/100000000000000 : ℝ)^6217 := by
    have hnat : (136707359 : ℕ)^8265*100000000000000^6217 ≤ 33316638932629^6217*312500000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136707359 312500000 33316638932629 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503273913/10000000000 : ℝ)^8265 ≤ (8656332241411/25000000000000 : ℝ)^6217 := by
    have hnat : (4503273913 : ℕ)^8265*25000000000000^6217 ≤ 8656332241411^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503273913 10000000000 8656332241411 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212486677/500000000 : ℝ)^8265 ≤ (200362700571/625000000000 : ℝ)^6217 := by
    have hnat : (212486677 : ℕ)^8265*625000000000^6217 ≤ 200362700571^6217*500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212486677 500000000 200362700571 625000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136707359/312500000 : ℝ), (4503273913/10000000000 : ℝ), (212486677/500000000 : ℝ)] ![(33316638932629/100000000000000 : ℝ), (8656332241411/25000000000000 : ℝ), (200362700571/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136707359/312500000 : ℝ)|^8265 ≤ (33316638932629/100000000000000 : ℝ)^6217
        have hw : |(136707359/312500000 : ℝ)|=(136707359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503273913/10000000000 : ℝ)|^8265 ≤ (8656332241411/25000000000000 : ℝ)^6217
        have hw : |(4503273913/10000000000 : ℝ)|=(4503273913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212486677/500000000 : ℝ)|^8265 ≤ (200362700571/625000000000 : ℝ)^6217
        have hw : |(212486677/500000000 : ℝ)|=(212486677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7009/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7009/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11249/100000 : ℝ) ^ (1033/256 : ℝ) ≤ (14828471634356001/100000000000000000000 : ℝ) := by
    have hpowers : (11249/100000 : ℝ)^1033 ≤ (14828471634356001/100000000000000000000 : ℝ)^256 := by
      have hnat : (11249 : ℕ)^1033*100000000000000000000^256 ≤ 14828471634356001^256*100000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11249 100000 14828471634356001 100000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11249/100000 : ℝ)) (X := (14828471634356001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7009/50000 : ℝ) ^ (1033/256 : ℝ) ≤ (36036690863386161/100000000000000000000 : ℝ) := by
    have hpowers : (7009/50000 : ℝ)^1033 ≤ (36036690863386161/100000000000000000000 : ℝ)^256 := by
      have hnat : (7009 : ℕ)^1033*100000000000000000000^256 ≤ 36036690863386161^256*50000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7009 50000 36036690863386161 100000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7009/50000 : ℝ)) (X := (36036690863386161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014828471634356001/50000000000000000000 : ℝ) ≤ (10000734881976611/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50014828471634356001/50000000000000000000 : ℝ)^256 ≤ (10000734881976611/10000000000000000 : ℝ)^1033 := by
      have hnat : (50014828471634356001 : ℕ)^256*10000000000000000^1033 ≤ 10000734881976611^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014828471634356001 50000000000000000000 10000734881976611 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000734881976611/10000000000000000 : ℝ)) (X := (50014828471634356001/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025432581248871081/50000000000000000000 : ℝ) ≤ (200025206178803/200000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50025432581248871081/50000000000000000000 : ℝ)^256 ≤ (200025206178803/200000000000000 : ℝ)^1033 := by
      have hnat : (50025432581248871081 : ℕ)^256*200000000000000^1033 ≤ 200025206178803^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025432581248871081 50000000000000000000 200025206178803 200000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200025206178803/200000000000000 : ℝ)) (X := (50025432581248871081/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036036690863386161/50000000000000000000 : ℝ) ≤ (10001785735903689/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50036036690863386161/50000000000000000000 : ℝ)^256 ≤ (10001785735903689/10000000000000000 : ℝ)^1033 := by
      have hnat : (50036036690863386161 : ℕ)^256*10000000000000000^1033 ≤ 10001785735903689^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036036690863386161 50000000000000000000 10001785735903689 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001785735903689/10000000000000000 : ℝ)) (X := (50036036690863386161/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14828471634356001/100000000000000000000 : ℝ) ≤ ((27680213832367535437/27690000000000000000 : ℝ)+2*(525426963539/276900000000000 : ℝ)*(11249/100000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (27680213832367535437/27690000000000000000 : ℝ)+2*(525426963539/276900000000000 : ℝ)*(11249/100000 : ℝ)=(10000734881976611/10000000000000000 : ℝ) by norm_num, show 1+2*(14828471634356001/100000000000000000000 : ℝ)=(50014828471634356001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36036690863386161/100000000000000000000 : ℝ)+(14828471634356001/100000000000000000000 : ℝ) ≤ ((27680213832367535437/27690000000000000000 : ℝ)+(525426963539/276900000000000 : ℝ)*((7009/50000 : ℝ)+(11249/100000 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (27680213832367535437/27690000000000000000 : ℝ)+(525426963539/276900000000000 : ℝ)*((7009/50000 : ℝ)+(11249/100000 : ℝ))=(200025206178803/200000000000000 : ℝ) by norm_num, show 1+(36036690863386161/100000000000000000000 : ℝ)+(14828471634356001/100000000000000000000 : ℝ)=(50025432581248871081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36036690863386161/100000000000000000000 : ℝ) ≤ ((27680213832367535437/27690000000000000000 : ℝ)+2*(525426963539/276900000000000 : ℝ)*(7009/50000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (27680213832367535437/27690000000000000000 : ℝ)+2*(525426963539/276900000000000 : ℝ)*(7009/50000 : ℝ)=(10001785735903689/10000000000000000 : ℝ) by norm_num, show 1+2*(36036690863386161/100000000000000000000 : ℝ)=(50036036690863386161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27680213832367535437/27690000000000000000 : ℝ)*(X 1 0+X 2 0)+(525426963539/276900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (27680213832367535437/27690000000000000000 : ℝ)) (alpha := (525426963539/276900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27680213832367535437/27690000000000000000 : ℝ)*(X 0 1+X 2 1)+(525426963539/276900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (27680213832367535437/27690000000000000000 : ℝ)) (alpha := (525426963539/276900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27680213832367535437/27690000000000000000 : ℝ)*(X 0 2+X 1 2)+(525426963539/276900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7009/50000 : ℝ)) (c := (27680213832367535437/27690000000000000000 : ℝ)) (alpha := (525426963539/276900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-220080883/1000000000 : ℝ)*X 0 0+(5394342967/10000000000 : ℝ)*X 0 1+(1316119357/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334061739/625000000 : ℝ)*X 1 0+(-1133348957/5000000000 : ℝ)*X 1 1+(2632238821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344987913/10000000000 : ℝ)*X 2 0+(5264477469/10000000000 : ℝ)*X 2 1+(-90667921/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374625541/10000000000 : ℝ)*X 0 0+(4249092031/10000000000 : ℝ)*X 0 1+(2251956557/5000000000 : ℝ)*X 0 2+(4374625541/10000000000 : ℝ)*X 1 0+(4249092031/10000000000 : ℝ)*X 1 1+(2251956557/5000000000 : ℝ)*X 1 2+(4374625541/10000000000 : ℝ)*X 2 0+(4249092031/10000000000 : ℝ)*X 2 1+(2251956557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2200813797/10000000000 : ℝ)*X 0 0+(105296067/200000000 : ℝ)*X 0 1+(1348503987/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332016357/625000000 : ℝ)*X 1 0+(-33393119/156250000 : ℝ)*X 1 1+(1348503987/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312261713/10000000000 : ℝ)*X 2 0+(5394015947/10000000000 : ℝ)*X 2 1+(-427431923/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136707359/312500000 : ℝ)*X 0 0+(4503273913/10000000000 : ℝ)*X 0 1+(212486677/500000000 : ℝ)*X 0 2+(136707359/312500000 : ℝ)*X 1 0+(4503273913/10000000000 : ℝ)*X 1 1+(212486677/500000000 : ℝ)*X 1 2+(136707359/312500000 : ℝ)*X 2 0+(4503273913/10000000000 : ℝ)*X 2 1+(212486677/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2143111687158151559458032799/461500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1204281111/100000000000000 : ℝ)*(base19) + (6254161/500000000000 : ℝ)*(base23) + (59865469/25000000000000 : ℝ)*(upper3) + (21825829/50000000000000 : ℝ)*(upper4) + (3768117/12500000000000 : ℝ)*(upper5) + (5812356813224013/100000000000000 : ℝ)*(major0) + (5812356813224013/100000000000000 : ℝ)*(major1) + (2906178406612007/50000000000000 : ℝ)*(major2) + (7700317827499053/100000000000000 : ℝ)*(sp0) + (1540070976664903/20000000000000 : ℝ)*(sp1) + (308014193470937/4000000000000 : ℝ)*(sp2) + (784867407803581/20000000000000 : ℝ)*(sp3) + (9565026643/25000000000000 : ℝ)*(sp4) + (20345031299/100000000000000 : ℝ)*(sp7) + (981089346012301/25000000000000 : ℝ)*(f.failure) + (3850178043802813/50000000000000 : ℝ)*(f.sum) + (64872241462883/27690000000000000000000000000 : ℝ)*base65 + (3598597947565551319/2769000000000000000000000000000000 : ℝ)*base68 + (16030056114382457941/1384500000000000000000000000000000 : ℝ)*base70 + (18575042869861551319/2769000000000000000000000000000000 : ℝ)*base72 + (126260481654473/27690000000000000000000000000 : ℝ)*base73 + (7848364011187457941/1384500000000000000000000000000000 : ℝ)*base76 + (145117227651270479/71000000000000000000000000000000 : ℝ)*base77 + (1598686566923729521/71000000000000000000000000000000 : ℝ)*base80 + (223983390869/177500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (31317673/2500000000000000000000 : ℝ)*base89 + (31317673/2500000000000000000000 : ℝ)*base91 + (6317673/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34493815255686346067781777/3550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1797472267/100000000000000 : ℝ)*(base19) + (979132127/50000000000000 : ℝ)*(base23) + (48518977/25000000000000 : ℝ)*(upper3) + (72358021/100000000000000 : ℝ)*(lower4) + (98801603/50000000000000 : ℝ)*(upper5) + (1168332648927327/20000000000000 : ℝ)*(major0) + (1168332648927327/20000000000000 : ℝ)*(major1) + (1168332648927327/20000000000000 : ℝ)*(major2) + (48930464743/100000000000000 : ℝ)*(sp1) + (26342099199/50000000000000 : ℝ)*(sp2) + (154783636293449/2000000000000 : ℝ)*(sp4) + (7739131086735441/100000000000000 : ℝ)*(sp5) + (3869563586104899/50000000000000 : ℝ)*(sp6) + (197207217535761/5000000000000 : ℝ)*(sp7) + (197207217535761/5000000000000 : ℝ)*(f.failure) + (154783636293449/2000000000000 : ℝ)*(f.sum) + (95399781583/71000000000000000000000000 : ℝ)*base66 + (160026535409422741/14200000000000000000000000000000 : ℝ)*base67 + (251269373241422741/14200000000000000000000000000000 : ℝ)*base69 + (178608822628622741/14200000000000000000000000000000 : ℝ)*base71 + (114650562683/14200000000000000000000000 : ℝ)*base74 + (158864911310622741/14200000000000000000000000000000 : ℝ)*base75 + (720181732177259/14200000000000000000000000000000 : ℝ)*base78 + (297399666083822741/14200000000000000000000000000000 : ℝ)*base79 + (150557719853/71000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6092253/500000000000000000000 : ℝ)*base89 + (6092253/500000000000000000000 : ℝ)*base91 + (6092253/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1072_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1072_s8_0 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-44016313/200000000 : ℝ)*x 0 + (337140483/625000000 : ℝ)*x 1 + (2632284159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44016313/200000000 : ℝ)^8265 ≤ (13366509598371/100000000000000 : ℝ)^6217 := by
    have hnat : (44016313 : ℕ)^8265*100000000000000^6217 ≤ 13366509598371^6217*200000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44016313 200000000 13366509598371 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337140483/625000000 : ℝ)^8265 ≤ (550216679631/1250000000000 : ℝ)^6217 := by
    have hnat : (337140483 : ℕ)^8265*1250000000000^6217 ≤ 550216679631^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337140483 625000000 550216679631 1250000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632284159/5000000000 : ℝ)^8265 ≤ (2130807801009/5000000000000 : ℝ)^6217 := by
    have hnat : (2632284159 : ℕ)^8265*5000000000000^6217 ≤ 2130807801009^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632284159 5000000000 2130807801009 5000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44016313/200000000 : ℝ), (337140483/625000000 : ℝ), (2632284159/5000000000 : ℝ)] ![(13366509598371/100000000000000 : ℝ), (550216679631/1250000000000 : ℝ), (2130807801009/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44016313/200000000 : ℝ)|^8265 ≤ (13366509598371/100000000000000 : ℝ)^6217
        have hw : |(-44016313/200000000 : ℝ)|=(44016313/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337140483/625000000 : ℝ)|^8265 ≤ (550216679631/1250000000000 : ℝ)^6217
        have hw : |(337140483/625000000 : ℝ)|=(337140483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632284159/5000000000 : ℝ)|^8265 ≤ (2130807801009/5000000000000 : ℝ)^6217
        have hw : |(2632284159/5000000000 : ℝ)|=(2632284159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_1 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267248223/500000000 : ℝ)*x 0 + (-1133304623/5000000000 : ℝ)*x 1 + (5264568297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267248223/500000000 : ℝ)^8265 ≤ (43483509299371/100000000000000 : ℝ)^6217 := by
    have hnat : (267248223 : ℕ)^8265*100000000000000^6217 ≤ 43483509299371^6217*500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267248223 500000000 43483509299371 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133304623/5000000000 : ℝ)^8265 ≤ (6950167441933/50000000000000 : ℝ)^6217 := by
    have hnat : (1133304623 : ℕ)^8265*50000000000000^6217 ≤ 6950167441933^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133304623 5000000000 6950167441933 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264568297/10000000000 : ℝ)^8265 ≤ (10654038948547/25000000000000 : ℝ)^6217 := by
    have hnat : (5264568297 : ℕ)^8265*25000000000000^6217 ≤ 10654038948547^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264568297 10000000000 10654038948547 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267248223/500000000 : ℝ), (-1133304623/5000000000 : ℝ), (5264568297/10000000000 : ℝ)] ![(43483509299371/100000000000000 : ℝ), (6950167441933/50000000000000 : ℝ), (10654038948547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267248223/500000000 : ℝ)|^8265 ≤ (43483509299371/100000000000000 : ℝ)^6217
        have hw : |(267248223/500000000 : ℝ)|=(267248223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133304623/5000000000 : ℝ)|^8265 ≤ (6950167441933/50000000000000 : ℝ)^6217
        have hw : |(-1133304623/5000000000 : ℝ)|=(1133304623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264568297/10000000000 : ℝ)|^8265 ≤ (10654038948547/25000000000000 : ℝ)^6217
        have hw : |(5264568297/10000000000 : ℝ)|=(5264568297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_2 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672482213/5000000000 : ℝ)*x 0 + (5264568361/10000000000 : ℝ)*x 1 + (-2266609207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672482213/5000000000 : ℝ)^8265 ≤ (679429827057/1562500000000 : ℝ)^6217 := by
    have hnat : (2672482213 : ℕ)^8265*1562500000000^6217 ≤ 679429827057^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672482213 5000000000 679429827057 1562500000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264568361/10000000000 : ℝ)^8265 ≤ (21308078241463/50000000000000 : ℝ)^6217 := by
    have hnat : (5264568361 : ℕ)^8265*50000000000000^6217 ≤ 21308078241463^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264568361 10000000000 21308078241463 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266609207/10000000000 : ℝ)^8265 ≤ (868770910369/6250000000000 : ℝ)^6217 := by
    have hnat : (2266609207 : ℕ)^8265*6250000000000^6217 ≤ 868770910369^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266609207 10000000000 868770910369 6250000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672482213/5000000000 : ℝ), (5264568361/10000000000 : ℝ), (-2266609207/10000000000 : ℝ)] ![(679429827057/1562500000000 : ℝ), (21308078241463/50000000000000 : ℝ), (868770910369/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672482213/5000000000 : ℝ)|^8265 ≤ (679429827057/1562500000000 : ℝ)^6217
        have hw : |(2672482213/5000000000 : ℝ)|=(2672482213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264568361/10000000000 : ℝ)|^8265 ≤ (21308078241463/50000000000000 : ℝ)^6217
        have hw : |(5264568361/10000000000 : ℝ)|=(5264568361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266609207/10000000000 : ℝ)|^8265 ≤ (868770910369/6250000000000 : ℝ)^6217
        have hw : |(-2266609207/10000000000 : ℝ)|=(2266609207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_3 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374630331/10000000000 : ℝ)*x 0 + (4249273729/10000000000 : ℝ)*x 1 + (2251865061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374630331/10000000000 : ℝ)^8265 ≤ (6663317343933/20000000000000 : ℝ)^6217 := by
    have hnat : (4374630331 : ℕ)^8265*20000000000000^6217 ≤ 6663317343933^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374630331 10000000000 6663317343933 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249273729/10000000000 : ℝ)^8265 ≤ (32053420946497/100000000000000 : ℝ)^6217 := by
    have hnat : (4249273729 : ℕ)^8265*100000000000000^6217 ≤ 32053420946497^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249273729 10000000000 32053420946497 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251865061/5000000000 : ℝ)^8265 ≤ (34629992322281/100000000000000 : ℝ)^6217 := by
    have hnat : (2251865061 : ℕ)^8265*100000000000000^6217 ≤ 34629992322281^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251865061 5000000000 34629992322281 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374630331/10000000000 : ℝ), (4249273729/10000000000 : ℝ), (2251865061/5000000000 : ℝ)] ![(6663317343933/20000000000000 : ℝ), (32053420946497/100000000000000 : ℝ), (34629992322281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374630331/10000000000 : ℝ)|^8265 ≤ (6663317343933/20000000000000 : ℝ)^6217
        have hw : |(4374630331/10000000000 : ℝ)|=(4374630331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249273729/10000000000 : ℝ)|^8265 ≤ (32053420946497/100000000000000 : ℝ)^6217
        have hw : |(4249273729/10000000000 : ℝ)|=(4249273729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251865061/5000000000 : ℝ)|^8265 ≤ (34629992322281/100000000000000 : ℝ)^6217
        have hw : |(2251865061/5000000000 : ℝ)|=(2251865061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_4 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-137551297/625000000 : ℝ)*x 0 + (5264893141/10000000000 : ℝ)*x 1 + (1078784339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137551297/625000000 : ℝ)^8265 ≤ (2673310158531/20000000000000 : ℝ)^6217 := by
    have hnat : (137551297 : ℕ)^8265*20000000000000^6217 ≤ 2673310158531^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137551297 625000000 2673310158531 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264893141/10000000000 : ℝ)^8265 ≤ (42619651643959/100000000000000 : ℝ)^6217 := by
    have hnat : (5264893141 : ℕ)^8265*100000000000000^6217 ≤ 42619651643959^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264893141 10000000000 42619651643959 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078784339/2000000000 : ℝ)^8265 ≤ (1100344938941/2500000000000 : ℝ)^6217 := by
    have hnat : (1078784339 : ℕ)^8265*2500000000000^6217 ≤ 1100344938941^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078784339 2000000000 1100344938941 2500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137551297/625000000 : ℝ), (5264893141/10000000000 : ℝ), (1078784339/2000000000 : ℝ)] ![(2673310158531/20000000000000 : ℝ), (42619651643959/100000000000000 : ℝ), (1100344938941/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137551297/625000000 : ℝ)|^8265 ≤ (2673310158531/20000000000000 : ℝ)^6217
        have hw : |(-137551297/625000000 : ℝ)|=(137551297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264893141/10000000000 : ℝ)|^8265 ≤ (42619651643959/100000000000000 : ℝ)^6217
        have hw : |(5264893141/10000000000 : ℝ)|=(5264893141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078784339/2000000000 : ℝ)|^8265 ≤ (1100344938941/2500000000000 : ℝ)^6217
        have hw : |(1078784339/2000000000 : ℝ)|=(1078784339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_5 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312285209/10000000000 : ℝ)*x 0 + (-427451139/2000000000 : ℝ)*x 1 + (337120109/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312285209/10000000000 : ℝ)^8265 ≤ (43130427218667/100000000000000 : ℝ)^6217 := by
    have hnat : (5312285209 : ℕ)^8265*100000000000000^6217 ≤ 43130427218667^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312285209 10000000000 43130427218667 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427451139/2000000000 : ℝ)^8265 ≤ (2571154934971/20000000000000 : ℝ)^6217 := by
    have hnat : (427451139 : ℕ)^8265*20000000000000^6217 ≤ 2571154934971^6217*2000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427451139 2000000000 2571154934971 20000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337120109/625000000 : ℝ)^8265 ≤ (44013798089187/100000000000000 : ℝ)^6217 := by
    have hnat : (337120109 : ℕ)^8265*100000000000000^6217 ≤ 44013798089187^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337120109 625000000 44013798089187 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312285209/10000000000 : ℝ), (-427451139/2000000000 : ℝ), (337120109/625000000 : ℝ)] ![(43130427218667/100000000000000 : ℝ), (2571154934971/20000000000000 : ℝ), (44013798089187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312285209/10000000000 : ℝ)|^8265 ≤ (43130427218667/100000000000000 : ℝ)^6217
        have hw : |(5312285209/10000000000 : ℝ)|=(5312285209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427451139/2000000000 : ℝ)|^8265 ≤ (2571154934971/20000000000000 : ℝ)^6217
        have hw : |(-427451139/2000000000 : ℝ)|=(427451139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337120109/625000000 : ℝ)|^8265 ≤ (44013798089187/100000000000000 : ℝ)^6217
        have hw : |(337120109/625000000 : ℝ)|=(337120109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_6 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332017809/625000000 : ℝ)*x 0 + (269696087/500000000 : ℝ)*x 1 + (-1068628029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332017809/625000000 : ℝ)^8265 ≤ (5391303044797/12500000000000 : ℝ)^6217 := by
    have hnat : (332017809 : ℕ)^8265*12500000000000^6217 ≤ 5391303044797^6217*625000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332017809 625000000 5391303044797 12500000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269696087/500000000 : ℝ)^8265 ≤ (11003449511449/25000000000000 : ℝ)^6217 := by
    have hnat : (269696087 : ℕ)^8265*25000000000000^6217 ≤ 11003449511449^6217*500000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269696087 500000000 11003449511449 25000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068628029/5000000000 : ℝ)^8265 ≤ (1285577757761/10000000000000 : ℝ)^6217 := by
    have hnat : (1068628029 : ℕ)^8265*10000000000000^6217 ≤ 1285577757761^6217*5000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068628029 5000000000 1285577757761 10000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332017809/625000000 : ℝ), (269696087/500000000 : ℝ), (-1068628029/5000000000 : ℝ)] ![(5391303044797/12500000000000 : ℝ), (11003449511449/25000000000000 : ℝ), (1285577757761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332017809/625000000 : ℝ)|^8265 ≤ (5391303044797/12500000000000 : ℝ)^6217
        have hw : |(332017809/625000000 : ℝ)|=(332017809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269696087/500000000 : ℝ)|^8265 ≤ (11003449511449/25000000000000 : ℝ)^6217
        have hw : |(269696087/500000000 : ℝ)|=(269696087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1068628029/5000000000 : ℝ)|^8265 ≤ (1285577757761/10000000000000 : ℝ)^6217
        have hw : |(-1068628029/5000000000 : ℝ)|=(1068628029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1072_s8_7 (p : ℝ) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374640031/10000000000 : ℝ)*x 0 + (90061853/200000000 : ℝ)*x 1 + (4249913707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374640031/10000000000 : ℝ)^8265 ≤ (33316684929057/100000000000000 : ℝ)^6217 := by
    have hnat : (4374640031 : ℕ)^8265*100000000000000^6217 ≤ 33316684929057^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374640031 10000000000 33316684929057 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90061853/200000000 : ℝ)^8265 ≤ (34623476143131/100000000000000 : ℝ)^6217 := by
    have hnat : (90061853 : ℕ)^8265*100000000000000^6217 ≤ 34623476143131^6217*200000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90061853 200000000 34623476143131 100000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249913707/10000000000 : ℝ)^8265 ≤ (16029919456803/50000000000000 : ℝ)^6217 := by
    have hnat : (4249913707 : ℕ)^8265*50000000000000^6217 ≤ 16029919456803^6217*10000000000^8265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249913707 10000000000 16029919456803 50000000000000 8265 6217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8265/2048 : ℝ)) 8265 6217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374640031/10000000000 : ℝ), (90061853/200000000 : ℝ), (4249913707/10000000000 : ℝ)] ![(33316684929057/100000000000000 : ℝ), (34623476143131/100000000000000 : ℝ), (16029919456803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374640031/10000000000 : ℝ)|^8265 ≤ (33316684929057/100000000000000 : ℝ)^6217
        have hw : |(4374640031/10000000000 : ℝ)|=(4374640031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90061853/200000000 : ℝ)|^8265 ≤ (34623476143131/100000000000000 : ℝ)^6217
        have hw : |(90061853/200000000 : ℝ)|=(90061853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249913707/10000000000 : ℝ)|^8265 ≤ (16029919456803/50000000000000 : ℝ)^6217
        have hw : |(4249913707/10000000000 : ℝ)|=(4249913707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1072_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (1033/256 : ℝ) ≤ (14876402206501783/100000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^1033 ≤ (14876402206501783/100000000000000000000 : ℝ)^256 := by
      have hnat : (5629 : ℕ)^1033*100000000000000000000^256 ≤ 14876402206501783^256*50000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 14876402206501783 100000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (14876402206501783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14009/100000 : ℝ) ^ (1033/256 : ℝ) ≤ (8985855400106351/25000000000000000000 : ℝ) := by
    have hpowers : (14009/100000 : ℝ)^1033 ≤ (8985855400106351/25000000000000000000 : ℝ)^256 := by
      have hnat : (14009 : ℕ)^1033*25000000000000000000^256 ≤ 8985855400106351^256*100000^1033 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14009 100000 8985855400106351 25000000000000000000 1033 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14009/100000 : ℝ)) (X := (8985855400106351/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014876402206501783/50000000000000000000 : ℝ) ≤ (1000073725709483/1000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (50014876402206501783/50000000000000000000 : ℝ)^256 ≤ (1000073725709483/1000000000000000 : ℝ)^1033 := by
      have hnat : (50014876402206501783 : ℕ)^256*1000000000000000^1033 ≤ 1000073725709483^1033*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014876402206501783 50000000000000000000 1000073725709483 1000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000073725709483/1000000000000000 : ℝ)) (X := (50014876402206501783/50000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050819823806927187/100000000000000000000 : ℝ) ≤ (10001259185777699/10000000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (100050819823806927187/100000000000000000000 : ℝ)^256 ≤ (10001259185777699/10000000000000000 : ℝ)^1033 := by
      have hnat : (100050819823806927187 : ℕ)^256*10000000000000000^1033 ≤ 10001259185777699^1033*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050819823806927187 100000000000000000000 10001259185777699 10000000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001259185777699/10000000000000000 : ℝ)) (X := (100050819823806927187/100000000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508985855400106351/12500000000000000000 : ℝ) ≤ (1250222639307571/1250000000000000 : ℝ) ^ (1033/256 : ℝ) := by
    have hpowers : (12508985855400106351/12500000000000000000 : ℝ)^256 ≤ (1250222639307571/1250000000000000 : ℝ)^1033 := by
      have hnat : (12508985855400106351 : ℕ)^256*1250000000000000^1033 ≤ 1250222639307571^1033*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508985855400106351 12500000000000000000 1250222639307571 1250000000000000 256 1033 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250222639307571/1250000000000000 : ℝ)) (X := (12508985855400106351/12500000000000000000 : ℝ)) (by norm_num) 1033 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14876402206501783/100000000000000000000 : ℝ) ≤ ((4583379408007399821/4585000000000000000 : ℝ)+2*(173976227623/91700000000000 : ℝ)*(5629/50000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (4583379408007399821/4585000000000000000 : ℝ)+2*(173976227623/91700000000000 : ℝ)*(5629/50000 : ℝ)=(1000073725709483/1000000000000000 : ℝ) by norm_num, show 1+2*(14876402206501783/100000000000000000000 : ℝ)=(50014876402206501783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8985855400106351/25000000000000000000 : ℝ)+(14876402206501783/100000000000000000000 : ℝ) ≤ ((4583379408007399821/4585000000000000000 : ℝ)+(173976227623/91700000000000 : ℝ)*((14009/100000 : ℝ)+(5629/50000 : ℝ)))^(1033/256 : ℝ) := by
    rw [show (4583379408007399821/4585000000000000000 : ℝ)+(173976227623/91700000000000 : ℝ)*((14009/100000 : ℝ)+(5629/50000 : ℝ))=(10001259185777699/10000000000000000 : ℝ) by norm_num, show 1+(8985855400106351/25000000000000000000 : ℝ)+(14876402206501783/100000000000000000000 : ℝ)=(100050819823806927187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8985855400106351/25000000000000000000 : ℝ) ≤ ((4583379408007399821/4585000000000000000 : ℝ)+2*(173976227623/91700000000000 : ℝ)*(14009/100000 : ℝ))^(1033/256 : ℝ) := by
    rw [show (4583379408007399821/4585000000000000000 : ℝ)+2*(173976227623/91700000000000 : ℝ)*(14009/100000 : ℝ)=(1250222639307571/1250000000000000 : ℝ) by norm_num, show 1+2*(8985855400106351/25000000000000000000 : ℝ)=(12508985855400106351/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4583379408007399821/4585000000000000000 : ℝ)*(X 1 0+X 2 0)+(173976227623/91700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (4583379408007399821/4585000000000000000 : ℝ)) (alpha := (173976227623/91700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4583379408007399821/4585000000000000000 : ℝ)*(X 0 1+X 2 1)+(173976227623/91700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (4583379408007399821/4585000000000000000 : ℝ)) (alpha := (173976227623/91700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4583379408007399821/4585000000000000000 : ℝ)*(X 0 2+X 1 2)+(173976227623/91700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1033/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (4583379408007399821/4585000000000000000 : ℝ)) (alpha := (173976227623/91700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-44016313/200000000 : ℝ)*X 0 0+(337140483/625000000 : ℝ)*X 0 1+(2632284159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267248223/500000000 : ℝ)*X 1 0+(-1133304623/5000000000 : ℝ)*X 1 1+(5264568297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672482213/5000000000 : ℝ)*X 2 0+(5264568361/10000000000 : ℝ)*X 2 1+(-2266609207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374630331/10000000000 : ℝ)*X 0 0+(4249273729/10000000000 : ℝ)*X 0 1+(2251865061/5000000000 : ℝ)*X 0 2+(4374630331/10000000000 : ℝ)*X 1 0+(4249273729/10000000000 : ℝ)*X 1 1+(2251865061/5000000000 : ℝ)*X 1 2+(4374630331/10000000000 : ℝ)*X 2 0+(4249273729/10000000000 : ℝ)*X 2 1+(2251865061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-137551297/625000000 : ℝ)*X 0 0+(5264893141/10000000000 : ℝ)*X 0 1+(1078784339/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312285209/10000000000 : ℝ)*X 1 0+(-427451139/2000000000 : ℝ)*X 1 1+(337120109/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332017809/625000000 : ℝ)*X 2 0+(269696087/500000000 : ℝ)*X 2 1+(-1068628029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374640031/10000000000 : ℝ)*X 0 0+(90061853/200000000 : ℝ)*X 0 1+(4249913707/10000000000 : ℝ)*X 0 2+(4374640031/10000000000 : ℝ)*X 1 0+(90061853/200000000 : ℝ)*X 1 1+(4249913707/10000000000 : ℝ)*X 1 2+(4374640031/10000000000 : ℝ)*X 2 0+(90061853/200000000 : ℝ)*X 2 1+(4249913707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1072_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1096687571078170572045133209/229250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252418181/25000000000000 : ℝ)*(base19) + (808998547/100000000000000 : ℝ)*(base23) + (81040951/100000000000000 : ℝ)*(lower2) + (61717261/50000000000000 : ℝ)*(upper3) + (31503571/50000000000000 : ℝ)*(upper5) + (181896129807183/3125000000000 : ℝ)*(major0) + (181896129807183/3125000000000 : ℝ)*(major1) + (5820676153829857/100000000000000 : ℝ)*(major2) + (7711351586000261/100000000000000 : ℝ)*(sp0) + (1927844186145479/25000000000000 : ℝ)*(sp1) + (7711376945256093/100000000000000 : ℝ)*(sp2) + (785991900653847/20000000000000 : ℝ)*(sp3) + (26168254379/100000000000000 : ℝ)*(sp4) + (1861334453/12500000000000 : ℝ)*(sp7) + (3929974393944859/100000000000000 : ℝ)*(f.failure) + (96392221928183/1250000000000 : ℝ)*(f.sum) + (24616043676871/9170000000000000000000000000 : ℝ)*base66 + (196453349463587861/28656250000000000000000000000000 : ℝ)*base67 + (753303196788879371/65500000000000000000000000000000 : ℝ)*base69 + (254504775886744111/28656250000000000000000000000000 : ℝ)*base71 + (10058504607231/9170000000000000000000000000 : ℝ)*base74 + (758154542779379371/65500000000000000000000000000000 : ℝ)*base75 + (32609787285048783/3582031250000000000000000000000 : ℝ)*base78 + (42508101397960757/14328125000000000000000000000000 : ℝ)*base80 + (14511506089107/4585000000000000000000000000 : ℝ)*base82 + (41007007/10000000000000000000000 : ℝ)*base89 + (41007007/10000000000000000000000 : ℝ)*base91 + (58992993/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (169365547968133959013613301/16375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1992803357/100000000000000 : ℝ)*(base19) + (714634897/50000000000000 : ℝ)*(base23) + (447427761/100000000000000 : ℝ)*(lower1) + (20797/2500000000000 : ℝ)*(upper2) + (13313699/10000000000000 : ℝ)*(upper3) + (233224707/100000000000000 : ℝ)*(upper5) + (5849970030279389/100000000000000 : ℝ)*(major0) + (5849970030279389/100000000000000 : ℝ)*(major1) + (5849970030279389/100000000000000 : ℝ)*(major2) + (7253613877/25000000000000 : ℝ)*(sp1) + (1550037366395853/20000000000000 : ℝ)*(sp4) + (19375389561801/250000000000 : ℝ)*(sp5) + (7750185402709471/100000000000000 : ℝ)*(sp6) + (1974876441907513/50000000000000 : ℝ)*(sp7) + (1974876441907513/50000000000000 : ℝ)*(f.failure) + (1550037366395853/20000000000000 : ℝ)*(f.sum) + (118480839909/655000000000000000000000000 : ℝ)*base66 + (1141990212760937233/65500000000000000000000000000000 : ℝ)*base68 + (1256787775613062767/65500000000000000000000000000000 : ℝ)*base69 + (667418793536437233/65500000000000000000000000000000 : ℝ)*base72 + (1403833869161/655000000000000000000000000 : ℝ)*base73 + (258918465602437233/65500000000000000000000000000000 : ℝ)*base76 + (1034722838568437233/65500000000000000000000000000000 : ℝ)*base78 + (406954333223437233/65500000000000000000000000000000 : ℝ)*base80 + (26181054572701/655000000000000000000000000 : ℝ)*base81 + (12575451/5000000000000000000000 : ℝ)*base90 + (12575451/5000000000000000000000 : ℝ)*base92 + (12575451/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1072_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1072_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1072_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1072_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1072_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1072_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1033/256 : ℝ) ≤ p) (hpb : p ≤ (8265/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148109773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1401/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1072_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
