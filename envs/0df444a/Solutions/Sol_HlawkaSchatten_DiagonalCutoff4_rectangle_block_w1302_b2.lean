-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1302_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:47.277266+00:00
-- url     : https://prove2.me/submissions/57cb438f-7b88-4945-9598-791deb0d215e

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
theorem support_rectangle_w1302_s6_0 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079031403/10000000000 : ℝ)*x 0 + (5414798057/10000000000 : ℝ)*x 1 + (327704407/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079031403/10000000000 : ℝ)^2131 ≤ (12651391425739/100000000000000 : ℝ)^1619 := by
    have hnat : (2079031403 : ℕ)^2131*100000000000000^1619 ≤ 12651391425739^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079031403 10000000000 12651391425739 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414798057/10000000000 : ℝ)^2131 ≤ (222997040691/500000000000 : ℝ)^1619 := by
    have hnat : (5414798057 : ℕ)^2131*500000000000^1619 ≤ 222997040691^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414798057 10000000000 222997040691 500000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327704407/625000000 : ℝ)^2131 ≤ (42749200418549/100000000000000 : ℝ)^1619 := by
    have hnat : (327704407 : ℕ)^2131*100000000000000^1619 ≤ 42749200418549^1619*625000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327704407 625000000 42749200418549 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079031403/10000000000 : ℝ), (5414798057/10000000000 : ℝ), (327704407/625000000 : ℝ)] ![(12651391425739/100000000000000 : ℝ), (222997040691/500000000000 : ℝ), (42749200418549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079031403/10000000000 : ℝ)|^2131 ≤ (12651391425739/100000000000000 : ℝ)^1619
        have hw : |(-2079031403/10000000000 : ℝ)|=(2079031403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414798057/10000000000 : ℝ)|^2131 ≤ (222997040691/500000000000 : ℝ)^1619
        have hw : |(5414798057/10000000000 : ℝ)|=(5414798057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327704407/625000000 : ℝ)|^2131 ≤ (42749200418549/100000000000000 : ℝ)^1619
        have hw : |(327704407/625000000 : ℝ)|=(327704407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_1 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349655693/10000000000 : ℝ)*x 0 + (-1083229943/5000000000 : ℝ)*x 1 + (1310817617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349655693/10000000000 : ℝ)^2131 ≤ (43894524013761/100000000000000 : ℝ)^1619 := by
    have hnat : (5349655693 : ℕ)^2131*100000000000000^1619 ≤ 43894524013761^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349655693 10000000000 43894524013761 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083229943/5000000000 : ℝ)^2131 ≤ (13356276026379/100000000000000 : ℝ)^1619 := by
    have hnat : (1083229943 : ℕ)^2131*100000000000000^1619 ≤ 13356276026379^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083229943 5000000000 13356276026379 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310817617/2500000000 : ℝ)^2131 ≤ (42749199946361/100000000000000 : ℝ)^1619 := by
    have hnat : (1310817617 : ℕ)^2131*100000000000000^1619 ≤ 42749199946361^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310817617 2500000000 42749199946361 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349655693/10000000000 : ℝ), (-1083229943/5000000000 : ℝ), (1310817617/2500000000 : ℝ)] ![(43894524013761/100000000000000 : ℝ), (13356276026379/100000000000000 : ℝ), (42749199946361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349655693/10000000000 : ℝ)|^2131 ≤ (43894524013761/100000000000000 : ℝ)^1619
        have hw : |(5349655693/10000000000 : ℝ)|=(5349655693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1083229943/5000000000 : ℝ)|^2131 ≤ (13356276026379/100000000000000 : ℝ)^1619
        have hw : |(-1083229943/5000000000 : ℝ)|=(1083229943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310817617/2500000000 : ℝ)|^2131 ≤ (42749199946361/100000000000000 : ℝ)^1619
        have hw : |(1310817617/2500000000 : ℝ)|=(1310817617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_2 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349655733/10000000000 : ℝ)*x 0 + (5243270541/10000000000 : ℝ)*x 1 + (-270807467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349655733/10000000000 : ℝ)^2131 ≤ (43894524445759/100000000000000 : ℝ)^1619 := by
    have hnat : (5349655733 : ℕ)^2131*100000000000000^1619 ≤ 43894524445759^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349655733 10000000000 43894524445759 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243270541/10000000000 : ℝ)^2131 ≤ (10687300182441/25000000000000 : ℝ)^1619 := by
    have hnat : (5243270541 : ℕ)^2131*25000000000000^1619 ≤ 10687300182441^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243270541 10000000000 10687300182441 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270807467/1250000000 : ℝ)^2131 ≤ (13356274809177/100000000000000 : ℝ)^1619 := by
    have hnat : (270807467 : ℕ)^2131*100000000000000^1619 ≤ 13356274809177^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270807467 1250000000 13356274809177 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349655733/10000000000 : ℝ), (5243270541/10000000000 : ℝ), (-270807467/1250000000 : ℝ)] ![(43894524445759/100000000000000 : ℝ), (10687300182441/25000000000000 : ℝ), (13356274809177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349655733/10000000000 : ℝ)|^2131 ≤ (43894524445759/100000000000000 : ℝ)^1619
        have hw : |(5349655733/10000000000 : ℝ)|=(5349655733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243270541/10000000000 : ℝ)|^2131 ≤ (10687300182441/25000000000000 : ℝ)^1619
        have hw : |(5243270541/10000000000 : ℝ)|=(5243270541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270807467/1250000000 : ℝ)|^2131 ≤ (13356274809177/100000000000000 : ℝ)^1619
        have hw : |(-270807467/1250000000 : ℝ)|=(270807467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_3 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4337184779/10000000000 : ℝ)*x 0 + (520460033/1250000000 : ℝ)*x 1 + (282347357/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337184779/10000000000 : ℝ)^2131 ≤ (33302504219077/100000000000000 : ℝ)^1619 := by
    have hnat : (4337184779 : ℕ)^2131*100000000000000^1619 ≤ 33302504219077^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337184779 10000000000 33302504219077 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520460033/1250000000 : ℝ)^2131 ≤ (31560156444121/100000000000000 : ℝ)^1619 := by
    have hnat : (520460033 : ℕ)^2131*100000000000000^1619 ≤ 31560156444121^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520460033 1250000000 31560156444121 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282347357/625000000 : ℝ)^2131 ≤ (3513733931721/10000000000000 : ℝ)^1619 := by
    have hnat : (282347357 : ℕ)^2131*10000000000000^1619 ≤ 3513733931721^1619*625000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282347357 625000000 3513733931721 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337184779/10000000000 : ℝ), (520460033/1250000000 : ℝ), (282347357/625000000 : ℝ)] ![(33302504219077/100000000000000 : ℝ), (31560156444121/100000000000000 : ℝ), (3513733931721/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337184779/10000000000 : ℝ)|^2131 ≤ (33302504219077/100000000000000 : ℝ)^1619
        have hw : |(4337184779/10000000000 : ℝ)|=(4337184779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520460033/1250000000 : ℝ)|^2131 ≤ (31560156444121/100000000000000 : ℝ)^1619
        have hw : |(520460033/1250000000 : ℝ)|=(520460033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282347357/625000000 : ℝ)|^2131 ≤ (3513733931721/10000000000000 : ℝ)^1619
        have hw : |(282347357/625000000 : ℝ)|=(282347357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_4 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079043987/10000000000 : ℝ)*x 0 + (41951063/80000000 : ℝ)*x 1 + (5414182577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079043987/10000000000 : ℝ)^2131 ≤ (6325746109671/50000000000000 : ℝ)^1619 := by
    have hnat : (2079043987 : ℕ)^2131*50000000000000^1619 ≤ 6325746109671^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079043987 10000000000 6325746109671 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41951063/80000000 : ℝ)^2131 ≤ (42755772142229/100000000000000 : ℝ)^1619 := by
    have hnat : (41951063 : ℕ)^2131*100000000000000^1619 ≤ 42755772142229^1619*80000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41951063 80000000 42755772142229 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414182577/10000000000 : ℝ)^2131 ≤ (4459273562301/10000000000000 : ℝ)^1619 := by
    have hnat : (5414182577 : ℕ)^2131*10000000000000^1619 ≤ 4459273562301^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414182577 10000000000 4459273562301 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079043987/10000000000 : ℝ), (41951063/80000000 : ℝ), (5414182577/10000000000 : ℝ)] ![(6325746109671/50000000000000 : ℝ), (42755772142229/100000000000000 : ℝ), (4459273562301/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079043987/10000000000 : ℝ)|^2131 ≤ (6325746109671/50000000000000 : ℝ)^1619
        have hw : |(-2079043987/10000000000 : ℝ)|=(2079043987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41951063/80000000 : ℝ)|^2131 ≤ (42755772142229/100000000000000 : ℝ)^1619
        have hw : |(41951063/80000000 : ℝ)|=(41951063/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414182577/10000000000 : ℝ)|^2131 ≤ (4459273562301/10000000000000 : ℝ)^1619
        have hw : |(5414182577/10000000000 : ℝ)|=(5414182577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_5 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305685117/10000000000 : ℝ)*x 0 + (-1995547753/10000000000 : ℝ)*x 1 + (216567303/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305685117/10000000000 : ℝ)^2131 ≤ (2713766438959/6250000000000 : ℝ)^1619 := by
    have hnat : (5305685117 : ℕ)^2131*6250000000000^1619 ≤ 2713766438959^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305685117 10000000000 2713766438959 6250000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1995547753/10000000000 : ℝ)^2131 ≤ (1498375170157/12500000000000 : ℝ)^1619 := by
    have hnat : (1995547753 : ℕ)^2131*12500000000000^1619 ≤ 1498375170157^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995547753 10000000000 1498375170157 12500000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216567303/400000000 : ℝ)^2131 ≤ (2787045975083/6250000000000 : ℝ)^1619 := by
    have hnat : (216567303 : ℕ)^2131*6250000000000^1619 ≤ 2787045975083^1619*400000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216567303 400000000 2787045975083 6250000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305685117/10000000000 : ℝ), (-1995547753/10000000000 : ℝ), (216567303/400000000 : ℝ)] ![(2713766438959/6250000000000 : ℝ), (1498375170157/12500000000000 : ℝ), (2787045975083/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305685117/10000000000 : ℝ)|^2131 ≤ (2713766438959/6250000000000 : ℝ)^1619
        have hw : |(5305685117/10000000000 : ℝ)|=(5305685117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1995547753/10000000000 : ℝ)|^2131 ≤ (1498375170157/12500000000000 : ℝ)^1619
        have hw : |(-1995547753/10000000000 : ℝ)|=(1995547753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216567303/400000000 : ℝ)|^2131 ≤ (2787045975083/6250000000000 : ℝ)^1619
        have hw : |(216567303/400000000 : ℝ)|=(216567303/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_6 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652842561/5000000000 : ℝ)*x 0 + (1353545643/2500000000 : ℝ)*x 1 + (-7982191/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652842561/5000000000 : ℝ)^2131 ≤ (43420263077203/100000000000000 : ℝ)^1619 := by
    have hnat : (2652842561 : ℕ)^2131*100000000000000^1619 ≤ 43420263077203^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652842561 5000000000 43420263077203 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353545643/2500000000 : ℝ)^2131 ≤ (8918547113761/20000000000000 : ℝ)^1619 := by
    have hnat : (1353545643 : ℕ)^2131*20000000000000^1619 ≤ 8918547113761^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353545643 2500000000 8918547113761 20000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7982191/40000000 : ℝ)^2131 ≤ (187296895899/1562500000000 : ℝ)^1619 := by
    have hnat : (7982191 : ℕ)^2131*1562500000000^1619 ≤ 187296895899^1619*40000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7982191 40000000 187296895899 1562500000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652842561/5000000000 : ℝ), (1353545643/2500000000 : ℝ), (-7982191/40000000 : ℝ)] ![(43420263077203/100000000000000 : ℝ), (8918547113761/20000000000000 : ℝ), (187296895899/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652842561/5000000000 : ℝ)|^2131 ≤ (43420263077203/100000000000000 : ℝ)^1619
        have hw : |(2652842561/5000000000 : ℝ)|=(2652842561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353545643/2500000000 : ℝ)|^2131 ≤ (8918547113761/20000000000000 : ℝ)^1619
        have hw : |(1353545643/2500000000 : ℝ)|=(1353545643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7982191/40000000 : ℝ)|^2131 ≤ (187296895899/1562500000000 : ℝ)^1619
        have hw : |(-7982191/40000000 : ℝ)|=(7982191/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s6_7 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (867442147/2000000000 : ℝ)*x 0 + (2258147181/5000000000 : ℝ)*x 1 + (520618777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867442147/2000000000 : ℝ)^2131 ≤ (33302766546531/100000000000000 : ℝ)^1619 := by
    have hnat : (867442147 : ℕ)^2131*100000000000000^1619 ≤ 33302766546531^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867442147 2000000000 33302766546531 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258147181/5000000000 : ℝ)^2131 ≤ (7024881221957/20000000000000 : ℝ)^1619 := by
    have hnat : (2258147181 : ℕ)^2131*20000000000000^1619 ≤ 7024881221957^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258147181 5000000000 7024881221957 20000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520618777/1250000000 : ℝ)^2131 ≤ (7893206829923/25000000000000 : ℝ)^1619 := by
    have hnat : (520618777 : ℕ)^2131*25000000000000^1619 ≤ 7893206829923^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520618777 1250000000 7893206829923 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867442147/2000000000 : ℝ), (2258147181/5000000000 : ℝ), (520618777/1250000000 : ℝ)] ![(33302766546531/100000000000000 : ℝ), (7024881221957/20000000000000 : ℝ), (7893206829923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867442147/2000000000 : ℝ)|^2131 ≤ (33302766546531/100000000000000 : ℝ)^1619
        have hw : |(867442147/2000000000 : ℝ)|=(867442147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258147181/5000000000 : ℝ)|^2131 ≤ (7024881221957/20000000000000 : ℝ)^1619
        have hw : |(2258147181/5000000000 : ℝ)|=(2258147181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520618777/1250000000 : ℝ)|^2131 ≤ (7893206829923/25000000000000 : ℝ)^1619
        have hw : |(520618777/1250000000 : ℝ)|=(520618777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1302_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14681/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11041/100000 : ℝ) ^ (4261/1024 : ℝ) ≤ (10419116476006983/100000000000000000000 : ℝ) := by
    have hpowers : (11041/100000 : ℝ)^4261 ≤ (10419116476006983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11041 : ℕ)^4261*100000000000000000000^1024 ≤ 10419116476006983^1024*100000^4261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11041 100000 10419116476006983 100000000000000000000 4261 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11041/100000 : ℝ)) (X := (10419116476006983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3673/25000 : ℝ) ^ (4261/1024 : ℝ) ≤ (34206850115468227/100000000000000000000 : ℝ) := by
    have hpowers : (3673/25000 : ℝ)^4261 ≤ (34206850115468227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3673 : ℕ)^4261*100000000000000000000^1024 ≤ 34206850115468227^1024*25000^4261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 25000 34206850115468227 100000000000000000000 4261 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/25000 : ℝ)) (X := (34206850115468227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010419116476006983/50000000000000000000 : ℝ) ≤ (500025037152987/500000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (50010419116476006983/50000000000000000000 : ℝ)^1024 ≤ (500025037152987/500000000000000 : ℝ)^4261 := by
      have hnat : (50010419116476006983 : ℕ)^1024*500000000000000^4261 ≤ 500025037152987^4261*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010419116476006983 50000000000000000000 500025037152987 500000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500025037152987/500000000000000 : ℝ)) (X := (50010419116476006983/50000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004462596659147521/10000000000000000000 : ℝ) ≤ (156266754153161/156250000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (10004462596659147521/10000000000000000000 : ℝ)^1024 ≤ (156266754153161/156250000000000 : ℝ)^4261 := by
      have hnat : (10004462596659147521 : ℕ)^1024*156250000000000^4261 ≤ 156266754153161^4261*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004462596659147521 10000000000000000000 156266754153161 156250000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156266754153161/156250000000000 : ℝ)) (X := (10004462596659147521/10000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034206850115468227/50000000000000000000 : ℝ) ≤ (2500410947136217/2500000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (50034206850115468227/50000000000000000000 : ℝ)^1024 ≤ (2500410947136217/2500000000000000 : ℝ)^4261 := by
      have hnat : (50034206850115468227 : ℕ)^1024*2500000000000000^4261 ≤ 2500410947136217^4261*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034206850115468227 50000000000000000000 2500410947136217 2500000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500410947136217/2500000000000000 : ℝ)) (X := (50034206850115468227/50000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10419116476006983/100000000000000000000 : ℝ) ≤ ((9124801961927453123/9127500000000000000 : ℝ)+2*(142880685641/91275000000000 : ℝ)*(11041/100000 : ℝ))^(4261/1024 : ℝ) := by
    rw [show (9124801961927453123/9127500000000000000 : ℝ)+2*(142880685641/91275000000000 : ℝ)*(11041/100000 : ℝ)=(500025037152987/500000000000000 : ℝ) by norm_num, show 1+2*(10419116476006983/100000000000000000000 : ℝ)=(50010419116476006983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34206850115468227/100000000000000000000 : ℝ)+(10419116476006983/100000000000000000000 : ℝ) ≤ ((9124801961927453123/9127500000000000000 : ℝ)+(142880685641/91275000000000 : ℝ)*((3673/25000 : ℝ)+(11041/100000 : ℝ)))^(4261/1024 : ℝ) := by
    rw [show (9124801961927453123/9127500000000000000 : ℝ)+(142880685641/91275000000000 : ℝ)*((3673/25000 : ℝ)+(11041/100000 : ℝ))=(156266754153161/156250000000000 : ℝ) by norm_num, show 1+(34206850115468227/100000000000000000000 : ℝ)+(10419116476006983/100000000000000000000 : ℝ)=(10004462596659147521/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34206850115468227/100000000000000000000 : ℝ) ≤ ((9124801961927453123/9127500000000000000 : ℝ)+2*(142880685641/91275000000000 : ℝ)*(3673/25000 : ℝ))^(4261/1024 : ℝ) := by
    rw [show (9124801961927453123/9127500000000000000 : ℝ)+2*(142880685641/91275000000000 : ℝ)*(3673/25000 : ℝ)=(2500410947136217/2500000000000000 : ℝ) by norm_num, show 1+2*(34206850115468227/100000000000000000000 : ℝ)=(50034206850115468227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9124801961927453123/9127500000000000000 : ℝ)*(X 1 0+X 2 0)+(142880685641/91275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (9124801961927453123/9127500000000000000 : ℝ)) (alpha := (142880685641/91275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9124801961927453123/9127500000000000000 : ℝ)*(X 0 1+X 2 1)+(142880685641/91275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (9124801961927453123/9127500000000000000 : ℝ)) (alpha := (142880685641/91275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9124801961927453123/9127500000000000000 : ℝ)*(X 0 2+X 1 2)+(142880685641/91275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (9124801961927453123/9127500000000000000 : ℝ)) (alpha := (142880685641/91275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2079031403/10000000000 : ℝ)*X 0 0+(5414798057/10000000000 : ℝ)*X 0 1+(327704407/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349655693/10000000000 : ℝ)*X 1 0+(-1083229943/5000000000 : ℝ)*X 1 1+(1310817617/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349655733/10000000000 : ℝ)*X 2 0+(5243270541/10000000000 : ℝ)*X 2 1+(-270807467/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4337184779/10000000000 : ℝ)*X 0 0+(520460033/1250000000 : ℝ)*X 0 1+(282347357/625000000 : ℝ)*X 0 2+(4337184779/10000000000 : ℝ)*X 1 0+(520460033/1250000000 : ℝ)*X 1 1+(282347357/625000000 : ℝ)*X 1 2+(4337184779/10000000000 : ℝ)*X 2 0+(520460033/1250000000 : ℝ)*X 2 1+(282347357/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2079043987/10000000000 : ℝ)*X 0 0+(41951063/80000000 : ℝ)*X 0 1+(5414182577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305685117/10000000000 : ℝ)*X 1 0+(-1995547753/10000000000 : ℝ)*X 1 1+(216567303/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652842561/5000000000 : ℝ)*X 2 0+(1353545643/2500000000 : ℝ)*X 2 1+(-7982191/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867442147/2000000000 : ℝ)*X 0 0+(2258147181/5000000000 : ℝ)*X 0 1+(520618777/1250000000 : ℝ)*X 0 2+(867442147/2000000000 : ℝ)*X 1 0+(2258147181/5000000000 : ℝ)*X 1 1+(520618777/1250000000 : ℝ)*X 1 2+(867442147/2000000000 : ℝ)*X 2 0+(2258147181/5000000000 : ℝ)*X 2 1+(520618777/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61185789698175182586407779/9507812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (272059839/20000000000000 : ℝ)*(base19) + (1314026393/100000000000000 : ℝ)*(base23) + (48074439/100000000000000 : ℝ)*(lower2) + (49499411/50000000000000 : ℝ)*(upper3) + (55017041/25000000000000 : ℝ)*(upper5) + (540992977289029/12500000000000 : ℝ)*(major0) + (540992977289029/12500000000000 : ℝ)*(major1) + (540992977289029/12500000000000 : ℝ)*(major2) + (1165998382521827/20000000000000 : ℝ)*(sp0) + (5830021118122551/100000000000000 : ℝ)*(sp1) + (728752645549419/12500000000000 : ℝ)*(sp2) + (2825851560341283/100000000000000 : ℝ)*(sp3) + (30565812611/100000000000000 : ℝ)*(sp4) + (3345837713/25000000000000 : ℝ)*(sp7) + (353233117961517/12500000000000 : ℝ)*(f.failure) + (2915011239210873/50000000000000 : ℝ)*(f.sum) + (2776422636977/18255000000000000000000000000 : ℝ)*base66 + (634296113814337567/114093750000000000000000000000000 : ℝ)*base67 + (475435803032193683/114093750000000000000000000000000 : ℝ)*base70 + (875873877199837567/114093750000000000000000000000000 : ℝ)*base71 + (2052736537201/9127500000000000000000000000 : ℝ)*base74 + (390225629722462567/114093750000000000000000000000000 : ℝ)*base75 + (250975346288381183/114093750000000000000000000000000 : ℝ)*base78 + (2010433531098337567/114093750000000000000000000000000 : ℝ)*base79 + (3682502789777/1140937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11257703/1250000000000000000000 : ℝ)*base89 + (11257703/1250000000000000000000 : ℝ)*base91 + (11257703/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206835523163809349154967503/76062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24056087/5000000000000 : ℝ)*(base19) + (532733917/100000000000000 : ℝ)*(base23) + (54270163/100000000000000 : ℝ)*(upper3) + (4130639/20000000000000 : ℝ)*(lower4) + (2273451/4000000000000 : ℝ)*(upper5) + (4359106383200939/100000000000000 : ℝ)*(major0) + (4359106383200939/100000000000000 : ℝ)*(major1) + (4359106383200939/100000000000000 : ℝ)*(major2) + (604071757/6250000000000 : ℝ)*(sp1) + (10528125963/100000000000000 : ℝ)*(sp2) + (5872000610345557/100000000000000 : ℝ)*(sp4) + (1174398092815141/20000000000000 : ℝ)*(sp5) + (5871989549485677/100000000000000 : ℝ)*(sp6) + (711553016353381/25000000000000 : ℝ)*(sp7) + (711553016353381/25000000000000 : ℝ)*(f.failure) + (5872000610345557/100000000000000 : ℝ)*(f.sum) + (75116639707559/18255000000000000000000000000 : ℝ)*base66 + (3339484521798732497/912750000000000000000000000000000 : ℝ)*base67 + (6445943795546232497/912750000000000000000000000000000 : ℝ)*base69 + (2493878984670767503/912750000000000000000000000000000 : ℝ)*base72 + (41792341846109/18255000000000000000000000000 : ℝ)*base74 + (7058730919620732497/912750000000000000000000000000000 : ℝ)*base75 + (4177128386036232497/912750000000000000000000000000000 : ℝ)*base77 + (119721609135732497/912750000000000000000000000000000 : ℝ)*base79 + (18038612659883/9127500000000000000000000000 : ℝ)*base81 + (15552079/2500000000000000000000 : ℝ)*base89 + (15552079/2500000000000000000000 : ℝ)*base91 + (15552079/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1302_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1302_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1302_s7_0 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-519760911/2500000000 : ℝ)*x 0 + (2707352171/5000000000 : ℝ)*x 1 + (104867121/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519760911/2500000000 : ℝ)^2131 ≤ (506059578881/4000000000000 : ℝ)^1619 := by
    have hnat : (519760911 : ℕ)^2131*4000000000000^1619 ≤ 506059578881^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519760911 2500000000 506059578881 4000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707352171/5000000000 : ℝ)^2131 ≤ (4459839214371/10000000000000 : ℝ)^1619 := by
    have hnat : (2707352171 : ℕ)^2131*10000000000000^1619 ≤ 4459839214371^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707352171 5000000000 4459839214371 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104867121/200000000 : ℝ)^2131 ≤ (8550023675197/20000000000000 : ℝ)^1619 := by
    have hnat : (104867121 : ℕ)^2131*20000000000000^1619 ≤ 8550023675197^1619*200000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104867121 200000000 8550023675197 20000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519760911/2500000000 : ℝ), (2707352171/5000000000 : ℝ), (104867121/200000000 : ℝ)] ![(506059578881/4000000000000 : ℝ), (4459839214371/10000000000000 : ℝ), (8550023675197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519760911/2500000000 : ℝ)|^2131 ≤ (506059578881/4000000000000 : ℝ)^1619
        have hw : |(-519760911/2500000000 : ℝ)|=(519760911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707352171/5000000000 : ℝ)|^2131 ≤ (4459839214371/10000000000000 : ℝ)^1619
        have hw : |(2707352171/5000000000 : ℝ)|=(2707352171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104867121/200000000 : ℝ)|^2131 ≤ (8550023675197/20000000000000 : ℝ)^1619
        have hw : |(104867121/200000000 : ℝ)|=(104867121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_1 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349631697/10000000000 : ℝ)*x 0 + (-216637803/1000000000 : ℝ)*x 1 + (163854891/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349631697/10000000000 : ℝ)^2131 ≤ (21947132429361/50000000000000 : ℝ)^1619 := by
    have hnat : (5349631697 : ℕ)^2131*50000000000000^1619 ≤ 21947132429361^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349631697 10000000000 21947132429361 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216637803/1000000000 : ℝ)^2131 ≤ (13355611795199/100000000000000 : ℝ)^1619 := by
    have hnat : (216637803 : ℕ)^2131*100000000000000^1619 ≤ 13355611795199^1619*1000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216637803 1000000000 13355611795199 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163854891/312500000 : ℝ)^2131 ≤ (8550024666797/20000000000000 : ℝ)^1619 := by
    have hnat : (163854891 : ℕ)^2131*20000000000000^1619 ≤ 8550024666797^1619*312500000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163854891 312500000 8550024666797 20000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349631697/10000000000 : ℝ), (-216637803/1000000000 : ℝ), (163854891/312500000 : ℝ)] ![(21947132429361/50000000000000 : ℝ), (13355611795199/100000000000000 : ℝ), (8550024666797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349631697/10000000000 : ℝ)|^2131 ≤ (21947132429361/50000000000000 : ℝ)^1619
        have hw : |(5349631697/10000000000 : ℝ)|=(5349631697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216637803/1000000000 : ℝ)|^2131 ≤ (13355611795199/100000000000000 : ℝ)^1619
        have hw : |(-216637803/1000000000 : ℝ)|=(216637803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163854891/312500000 : ℝ)|^2131 ≤ (8550024666797/20000000000000 : ℝ)^1619
        have hw : |(163854891/312500000 : ℝ)|=(163854891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_2 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069926189/2000000000 : ℝ)*x 0 + (1048671529/2000000000 : ℝ)*x 1 + (-2166377533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069926189/2000000000 : ℝ)^2131 ≤ (43894256737183/100000000000000 : ℝ)^1619 := by
    have hnat : (1069926189 : ℕ)^2131*100000000000000^1619 ≤ 43894256737183^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069926189 2000000000 43894256737183 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048671529/2000000000 : ℝ)^2131 ≤ (10687533873223/25000000000000 : ℝ)^1619 := by
    have hnat : (1048671529 : ℕ)^2131*25000000000000^1619 ≤ 10687533873223^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048671529 2000000000 10687533873223 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166377533/10000000000 : ℝ)^2131 ≤ (3338901940563/25000000000000 : ℝ)^1619 := by
    have hnat : (2166377533 : ℕ)^2131*25000000000000^1619 ≤ 3338901940563^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166377533 10000000000 3338901940563 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069926189/2000000000 : ℝ), (1048671529/2000000000 : ℝ), (-2166377533/10000000000 : ℝ)] ![(43894256737183/100000000000000 : ℝ), (10687533873223/25000000000000 : ℝ), (3338901940563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069926189/2000000000 : ℝ)|^2131 ≤ (43894256737183/100000000000000 : ℝ)^1619
        have hw : |(1069926189/2000000000 : ℝ)|=(1069926189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048671529/2000000000 : ℝ)|^2131 ≤ (10687533873223/25000000000000 : ℝ)^1619
        have hw : |(1048671529/2000000000 : ℝ)|=(1048671529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166377533/10000000000 : ℝ)|^2131 ≤ (3338901940563/25000000000000 : ℝ)^1619
        have hw : |(-2166377533/10000000000 : ℝ)|=(2166377533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_3 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2168596417/5000000000 : ℝ)*x 0 + (4163863307/10000000000 : ℝ)*x 1 + (4517371377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168596417/5000000000 : ℝ)^2131 ≤ (2081411601741/6250000000000 : ℝ)^1619 := by
    have hnat : (2168596417 : ℕ)^2131*6250000000000^1619 ≤ 2081411601741^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168596417 5000000000 2081411601741 6250000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4163863307/10000000000 : ℝ)^2131 ≤ (7890495667529/25000000000000 : ℝ)^1619 := by
    have hnat : (4163863307 : ℕ)^2131*25000000000000^1619 ≤ 7890495667529^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163863307 10000000000 7890495667529 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517371377/10000000000 : ℝ)^2131 ≤ (35135431690611/100000000000000 : ℝ)^1619 := by
    have hnat : (4517371377 : ℕ)^2131*100000000000000^1619 ≤ 35135431690611^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517371377 10000000000 35135431690611 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168596417/5000000000 : ℝ), (4163863307/10000000000 : ℝ), (4517371377/10000000000 : ℝ)] ![(2081411601741/6250000000000 : ℝ), (7890495667529/25000000000000 : ℝ), (35135431690611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168596417/5000000000 : ℝ)|^2131 ≤ (2081411601741/6250000000000 : ℝ)^1619
        have hw : |(2168596417/5000000000 : ℝ)|=(2168596417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4163863307/10000000000 : ℝ)|^2131 ≤ (7890495667529/25000000000000 : ℝ)^1619
        have hw : |(4163863307/10000000000 : ℝ)|=(4163863307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517371377/10000000000 : ℝ)|^2131 ≤ (35135431690611/100000000000000 : ℝ)^1619
        have hw : |(4517371377/10000000000 : ℝ)|=(4517371377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_4 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079055767/10000000000 : ℝ)*x 0 + (2621983819/5000000000 : ℝ)*x 1 + (2707044981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079055767/10000000000 : ℝ)^2131 ≤ (253031731467/2000000000000 : ℝ)^1619 := by
    have hnat : (2079055767 : ℕ)^2131*2000000000000^1619 ≤ 253031731467^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079055767 10000000000 253031731467 2000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621983819/5000000000 : ℝ)^2131 ≤ (42756681816269/100000000000000 : ℝ)^1619 := by
    have hnat : (2621983819 : ℕ)^2131*100000000000000^1619 ≤ 42756681816269^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621983819 5000000000 42756681816269 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707044981/5000000000 : ℝ)^2131 ≤ (11147932897509/25000000000000 : ℝ)^1619 := by
    have hnat : (2707044981 : ℕ)^2131*25000000000000^1619 ≤ 11147932897509^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707044981 5000000000 11147932897509 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079055767/10000000000 : ℝ), (2621983819/5000000000 : ℝ), (2707044981/5000000000 : ℝ)] ![(253031731467/2000000000000 : ℝ), (42756681816269/100000000000000 : ℝ), (11147932897509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079055767/10000000000 : ℝ)|^2131 ≤ (253031731467/2000000000000 : ℝ)^1619
        have hw : |(-2079055767/10000000000 : ℝ)|=(2079055767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621983819/5000000000 : ℝ)|^2131 ≤ (42756681816269/100000000000000 : ℝ)^1619
        have hw : |(2621983819/5000000000 : ℝ)|=(2621983819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707044981/5000000000 : ℝ)|^2131 ≤ (11147932897509/25000000000000 : ℝ)^1619
        have hw : |(2707044981/5000000000 : ℝ)|=(2707044981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_5 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165803349/312500000 : ℝ)*x 0 + (-1995644719/10000000000 : ℝ)*x 1 + (676761243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803349/312500000 : ℝ)^2131 ≤ (21710250276039/50000000000000 : ℝ)^1619 := by
    have hnat : (165803349 : ℕ)^2131*50000000000000^1619 ≤ 21710250276039^1619*312500000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803349 312500000 21710250276039 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1995644719/10000000000 : ℝ)^2131 ≤ (11987768030159/100000000000000 : ℝ)^1619 := by
    have hnat : (1995644719 : ℕ)^2131*100000000000000^1619 ≤ 11987768030159^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995644719 10000000000 11987768030159 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676761243/1250000000 : ℝ)^2131 ≤ (445917313949/1000000000000 : ℝ)^1619 := by
    have hnat : (676761243 : ℕ)^2131*1000000000000^1619 ≤ 445917313949^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676761243 1250000000 445917313949 1000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803349/312500000 : ℝ), (-1995644719/10000000000 : ℝ), (676761243/1250000000 : ℝ)] ![(21710250276039/50000000000000 : ℝ), (11987768030159/100000000000000 : ℝ), (445917313949/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803349/312500000 : ℝ)|^2131 ≤ (21710250276039/50000000000000 : ℝ)^1619
        have hw : |(165803349/312500000 : ℝ)|=(165803349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1995644719/10000000000 : ℝ)|^2131 ≤ (11987768030159/100000000000000 : ℝ)^1619
        have hw : |(-1995644719/10000000000 : ℝ)|=(1995644719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676761243/1250000000 : ℝ)|^2131 ≤ (445917313949/1000000000000 : ℝ)^1619
        have hw : |(676761243/1250000000 : ℝ)|=(676761243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_6 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305707097/10000000000 : ℝ)*x 0 + (338380627/625000000 : ℝ)*x 1 + (-249455587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305707097/10000000000 : ℝ)^2131 ≤ (542756247341/1250000000000 : ℝ)^1619 := by
    have hnat : (5305707097 : ℕ)^2131*1250000000000^1619 ≤ 542756247341^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305707097 10000000000 542756247341 1250000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338380627/625000000 : ℝ)^2131 ≤ (44591732348899/100000000000000 : ℝ)^1619 := by
    have hnat : (338380627 : ℕ)^2131*100000000000000^1619 ≤ 44591732348899^1619*625000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338380627 625000000 44591732348899 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249455587/1250000000 : ℝ)^2131 ≤ (11987767848307/100000000000000 : ℝ)^1619 := by
    have hnat : (249455587 : ℕ)^2131*100000000000000^1619 ≤ 11987767848307^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249455587 1250000000 11987767848307 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305707097/10000000000 : ℝ), (338380627/625000000 : ℝ), (-249455587/1250000000 : ℝ)] ![(542756247341/1250000000000 : ℝ), (44591732348899/100000000000000 : ℝ), (11987767848307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305707097/10000000000 : ℝ)|^2131 ≤ (542756247341/1250000000000 : ℝ)^1619
        have hw : |(5305707097/10000000000 : ℝ)|=(5305707097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338380627/625000000 : ℝ)|^2131 ≤ (44591732348899/100000000000000 : ℝ)^1619
        have hw : |(338380627/625000000 : ℝ)|=(338380627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249455587/1250000000 : ℝ)|^2131 ≤ (11987767848307/100000000000000 : ℝ)^1619
        have hw : |(-249455587/1250000000 : ℝ)|=(249455587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_s7_7 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (216860851/500000000 : ℝ)*x 0 + (141128457/312500000 : ℝ)*x 1 + (4165132353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216860851/500000000 : ℝ)^2131 ≤ (33302830066719/100000000000000 : ℝ)^1619 := by
    have hnat : (216860851 : ℕ)^2131*100000000000000^1619 ≤ 33302830066719^1619*500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216860851 500000000 33302830066719 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141128457/312500000 : ℝ)^2131 ≤ (17561262618243/50000000000000 : ℝ)^1619 := by
    have hnat : (141128457 : ℕ)^2131*50000000000000^1619 ≤ 17561262618243^1619*312500000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141128457 312500000 17561262618243 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165132353/10000000000 : ℝ)^2131 ≤ (31574644681691/100000000000000 : ℝ)^1619 := by
    have hnat : (4165132353 : ℕ)^2131*100000000000000^1619 ≤ 31574644681691^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165132353 10000000000 31574644681691 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216860851/500000000 : ℝ), (141128457/312500000 : ℝ), (4165132353/10000000000 : ℝ)] ![(33302830066719/100000000000000 : ℝ), (17561262618243/50000000000000 : ℝ), (31574644681691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216860851/500000000 : ℝ)|^2131 ≤ (33302830066719/100000000000000 : ℝ)^1619
        have hw : |(216860851/500000000 : ℝ)|=(216860851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141128457/312500000 : ℝ)|^2131 ≤ (17561262618243/50000000000000 : ℝ)^1619
        have hw : |(141128457/312500000 : ℝ)|=(141128457/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165132353/10000000000 : ℝ)|^2131 ≤ (31574644681691/100000000000000 : ℝ)^1619
        have hw : |(4165132353/10000000000 : ℝ)|=(4165132353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1302_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11053/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11051/100000 : ℝ) ^ (4261/1024 : ℝ) ≤ (1045844029899207/10000000000000000000 : ℝ) := by
    have hpowers : (11051/100000 : ℝ)^4261 ≤ (1045844029899207/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11051 : ℕ)^4261*10000000000000000000^1024 ≤ 1045844029899207^1024*100000^4261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11051 100000 1045844029899207 10000000000000000000 4261 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11051/100000 : ℝ)) (X := (1045844029899207/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14681/100000 : ℝ) ^ (4261/1024 : ℝ) ≤ (34100405802031597/100000000000000000000 : ℝ) := by
    have hpowers : (14681/100000 : ℝ)^4261 ≤ (34100405802031597/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14681 : ℕ)^4261*100000000000000000000^1024 ≤ 34100405802031597^1024*100000^4261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14681 100000 34100405802031597 100000000000000000000 4261 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14681/100000 : ℝ)) (X := (34100405802031597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001045844029899207/5000000000000000000 : ℝ) ≤ (5000251316406879/5000000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (5001045844029899207/5000000000000000000 : ℝ)^1024 ≤ (5000251316406879/5000000000000000 : ℝ)^4261 := by
      have hnat : (5001045844029899207 : ℕ)^1024*5000000000000000^4261 ≤ 5000251316406879^4261*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001045844029899207 5000000000000000000 5000251316406879 5000000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000251316406879/5000000000000000 : ℝ)) (X := (5001045844029899207/5000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044558846101023667/100000000000000000000 : ℝ) ≤ (10001070653314439/10000000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (100044558846101023667/100000000000000000000 : ℝ)^1024 ≤ (10001070653314439/10000000000000000 : ℝ)^4261 := by
      have hnat : (100044558846101023667 : ℕ)^1024*10000000000000000^4261 ≤ 10001070653314439^4261*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044558846101023667 100000000000000000000 10001070653314439 10000000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001070653314439/10000000000000000 : ℝ)) (X := (100044558846101023667/100000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034100405802031597/50000000000000000000 : ℝ) ≤ (125020483422689/125000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (50034100405802031597/50000000000000000000 : ℝ)^1024 ≤ (125020483422689/125000000000000 : ℝ)^4261 := by
      have hnat : (50034100405802031597 : ℕ)^1024*125000000000000^4261 ≤ 125020483422689^4261*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034100405802031597 50000000000000000000 125020483422689 125000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125020483422689/125000000000000 : ℝ)) (X := (50034100405802031597/50000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1045844029899207/10000000000000000000 : ℝ) ≤ ((18144635084003945039/18150000000000000000 : ℝ)+2*(568020500681/363000000000000 : ℝ)*(11051/100000 : ℝ))^(4261/1024 : ℝ) := by
    rw [show (18144635084003945039/18150000000000000000 : ℝ)+2*(568020500681/363000000000000 : ℝ)*(11051/100000 : ℝ)=(5000251316406879/5000000000000000 : ℝ) by norm_num, show 1+2*(1045844029899207/10000000000000000000 : ℝ)=(5001045844029899207/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34100405802031597/100000000000000000000 : ℝ)+(1045844029899207/10000000000000000000 : ℝ) ≤ ((18144635084003945039/18150000000000000000 : ℝ)+(568020500681/363000000000000 : ℝ)*((14681/100000 : ℝ)+(11051/100000 : ℝ)))^(4261/1024 : ℝ) := by
    rw [show (18144635084003945039/18150000000000000000 : ℝ)+(568020500681/363000000000000 : ℝ)*((14681/100000 : ℝ)+(11051/100000 : ℝ))=(10001070653314439/10000000000000000 : ℝ) by norm_num, show 1+(34100405802031597/100000000000000000000 : ℝ)+(1045844029899207/10000000000000000000 : ℝ)=(100044558846101023667/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34100405802031597/100000000000000000000 : ℝ) ≤ ((18144635084003945039/18150000000000000000 : ℝ)+2*(568020500681/363000000000000 : ℝ)*(14681/100000 : ℝ))^(4261/1024 : ℝ) := by
    rw [show (18144635084003945039/18150000000000000000 : ℝ)+2*(568020500681/363000000000000 : ℝ)*(14681/100000 : ℝ)=(125020483422689/125000000000000 : ℝ) by norm_num, show 1+2*(34100405802031597/100000000000000000000 : ℝ)=(50034100405802031597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18144635084003945039/18150000000000000000 : ℝ)*(X 1 0+X 2 0)+(568020500681/363000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18144635084003945039/18150000000000000000 : ℝ)) (alpha := (568020500681/363000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18144635084003945039/18150000000000000000 : ℝ)*(X 0 1+X 2 1)+(568020500681/363000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18144635084003945039/18150000000000000000 : ℝ)) (alpha := (568020500681/363000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18144635084003945039/18150000000000000000 : ℝ)*(X 0 2+X 1 2)+(568020500681/363000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (18144635084003945039/18150000000000000000 : ℝ)) (alpha := (568020500681/363000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-519760911/2500000000 : ℝ)*X 0 0+(2707352171/5000000000 : ℝ)*X 0 1+(104867121/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349631697/10000000000 : ℝ)*X 1 0+(-216637803/1000000000 : ℝ)*X 1 1+(163854891/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069926189/2000000000 : ℝ)*X 2 0+(1048671529/2000000000 : ℝ)*X 2 1+(-2166377533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2168596417/5000000000 : ℝ)*X 0 0+(4163863307/10000000000 : ℝ)*X 0 1+(4517371377/10000000000 : ℝ)*X 0 2+(2168596417/5000000000 : ℝ)*X 1 0+(4163863307/10000000000 : ℝ)*X 1 1+(4517371377/10000000000 : ℝ)*X 1 2+(2168596417/5000000000 : ℝ)*X 2 0+(4163863307/10000000000 : ℝ)*X 2 1+(4517371377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2079055767/10000000000 : ℝ)*X 0 0+(2621983819/5000000000 : ℝ)*X 0 1+(2707044981/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165803349/312500000 : ℝ)*X 1 0+(-1995644719/10000000000 : ℝ)*X 1 1+(676761243/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305707097/10000000000 : ℝ)*X 2 0+(338380627/625000000 : ℝ)*X 2 1+(-249455587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216860851/500000000 : ℝ)*X 0 0+(141128457/312500000 : ℝ)*X 0 1+(4165132353/10000000000 : ℝ)*X 0 2+(216860851/500000000 : ℝ)*X 1 0+(141128457/312500000 : ℝ)*X 1 1+(4165132353/10000000000 : ℝ)*X 1 2+(216860851/500000000 : ℝ)*X 2 0+(141128457/312500000 : ℝ)*X 2 1+(4165132353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10793178703029455010327/6050000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304643643/12500000000000 : ℝ)*(base19) + (1091643909/100000000000000 : ℝ)*(base23) + (28091467/10000000000000 : ℝ)*(lower2) + (96989591/25000000000000 : ℝ)*(upper3) + (349651/78125000000 : ℝ)*(upper5) + (4332518928583489/100000000000000 : ℝ)*(major0) + (4332518928583489/100000000000000 : ℝ)*(major1) + (4332518928583489/100000000000000 : ℝ)*(major2) + (5836124637036537/100000000000000 : ℝ)*(sp0) + (5836183168347647/100000000000000 : ℝ)*(sp1) + (5836184513852883/100000000000000 : ℝ)*(sp2) + (11315286872667/400000000000 : ℝ)*(sp3) + (30484230127/50000000000000 : ℝ)*(sp4) + (7618509219/25000000000000 : ℝ)*(sp7) + (1414426096101813/50000000000000 : ℝ)*(f.failure) + (729523200687099/12500000000000 : ℝ)*(f.sum) + (100533984882091/18150000000000000000000000000 : ℝ)*base66 + (674763007940229643/605000000000000000000000000000000 : ℝ)*base68 + (167117548520229643/605000000000000000000000000000000 : ℝ)*base70 + (2220616105664770357/605000000000000000000000000000000 : ℝ)*base71 + (39976947115591/18150000000000000000000000000 : ℝ)*base74 + (7667657821549770357/605000000000000000000000000000000 : ℝ)*base75 + (542840867315229643/605000000000000000000000000000000 : ℝ)*base78 + (4823757210514770357/605000000000000000000000000000000 : ℝ)*base79 + (30293357196841/18150000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (50703233/5000000000000000000000 : ℝ)*base90 + (50703233/5000000000000000000000 : ℝ)*base92 + (50703233/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13364357152127901293181/6050000000000000000000000000 : ℝ) := by norm_num
    linear_combination (451145171/100000000000000 : ℝ)*(base19) + (245809789/50000000000000 : ℝ)*(base23) + (84360827/50000000000000 : ℝ)*(lower1) + (13794431/50000000000000 : ℝ)*(upper3) + (10153427/20000000000000 : ℝ)*(lower4) + (958857/6250000000000 : ℝ)*(upper5) + (4363642738431917/100000000000000 : ℝ)*(major0) + (4363642738431917/100000000000000 : ℝ)*(major1) + (4363642738431917/100000000000000 : ℝ)*(major2) + (354078343/12500000000000 : ℝ)*(sp2) + (5878111393818783/100000000000000 : ℝ)*(sp4) + (1469527735668403/25000000000000 : ℝ)*(sp5) + (2939054034786231/50000000000000 : ℝ)*(sp6) + (1424587004706111/50000000000000 : ℝ)*(sp7) + (1424587004706111/50000000000000 : ℝ)*(f.failure) + (5878111393818783/100000000000000 : ℝ)*(f.sum) + (86256875218373/18150000000000000000000000000 : ℝ)*base66 + (2490998642218419921/605000000000000000000000000000000 : ℝ)*base67 + (6726916106568419921/605000000000000000000000000000000 : ℝ)*base69 + (417041653051580079/605000000000000000000000000000000 : ℝ)*base72 + (8862455089523/18150000000000000000000000000 : ℝ)*base74 + (119264790041580079/605000000000000000000000000000000 : ℝ)*base76 + (1728708774758419921/605000000000000000000000000000000 : ℝ)*base77 + (4352284684331580079/605000000000000000000000000000000 : ℝ)*base80 + (113590183219823/18150000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (24578851/5000000000000000000000 : ℝ)*base90 + (24578851/5000000000000000000000 : ℝ)*base92 + (24578851/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1302_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11053/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1302_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1302_box_0 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908536419/10000000000 : ℝ)*x 0 + (5391600089/10000000000 : ℝ)*x 1 + (2695800093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908536419/10000000000 : ℝ)^2131 ≤ (11303836233949/100000000000000 : ℝ)^1619 := by
    have hnat : (1908536419 : ℕ)^2131*100000000000000^1619 ≤ 11303836233949^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908536419 10000000000 11303836233949 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391600089/10000000000 : ℝ)^2131 ≤ (4434808134631/10000000000000 : ℝ)^1619 := by
    have hnat : (5391600089 : ℕ)^2131*10000000000000^1619 ≤ 4434808134631^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391600089 10000000000 4434808134631 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695800093/5000000000 : ℝ)^2131 ≤ (8869616479299/20000000000000 : ℝ)^1619 := by
    have hnat : (2695800093 : ℕ)^2131*20000000000000^1619 ≤ 8869616479299^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695800093 5000000000 8869616479299 20000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908536419/10000000000 : ℝ), (5391600089/10000000000 : ℝ), (2695800093/5000000000 : ℝ)] ![(11303836233949/100000000000000 : ℝ), (4434808134631/10000000000000 : ℝ), (8869616479299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908536419/10000000000 : ℝ)|^2131 ≤ (11303836233949/100000000000000 : ℝ)^1619
        have hw : |(-1908536419/10000000000 : ℝ)|=(1908536419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391600089/10000000000 : ℝ)|^2131 ≤ (4434808134631/10000000000000 : ℝ)^1619
        have hw : |(5391600089/10000000000 : ℝ)|=(5391600089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695800093/5000000000 : ℝ)|^2131 ≤ (8869616479299/20000000000000 : ℝ)^1619
        have hw : |(2695800093/5000000000 : ℝ)|=(2695800093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_1 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660568213/1250000000 : ℝ)*x 0 + (-513748667/2500000000 : ℝ)*x 1 + (5391600351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660568213/1250000000 : ℝ)^2131 ≤ (21596348725579/50000000000000 : ℝ)^1619 := by
    have hnat : (660568213 : ℕ)^2131*50000000000000^1619 ≤ 21596348725579^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660568213 1250000000 21596348725579 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513748667/2500000000 : ℝ)^2131 ≤ (12459218350713/100000000000000 : ℝ)^1619 := by
    have hnat : (513748667 : ℕ)^2131*100000000000000^1619 ≤ 12459218350713^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513748667 2500000000 12459218350713 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391600351/10000000000 : ℝ)^2131 ≤ (4434808418289/10000000000000 : ℝ)^1619 := by
    have hnat : (5391600351 : ℕ)^2131*10000000000000^1619 ≤ 4434808418289^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391600351 10000000000 4434808418289 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660568213/1250000000 : ℝ), (-513748667/2500000000 : ℝ), (5391600351/10000000000 : ℝ)] ![(21596348725579/50000000000000 : ℝ), (12459218350713/100000000000000 : ℝ), (4434808418289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660568213/1250000000 : ℝ)|^2131 ≤ (21596348725579/50000000000000 : ℝ)^1619
        have hw : |(660568213/1250000000 : ℝ)|=(660568213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513748667/2500000000 : ℝ)|^2131 ≤ (12459218350713/100000000000000 : ℝ)^1619
        have hw : |(-513748667/2500000000 : ℝ)|=(513748667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391600351/10000000000 : ℝ)|^2131 ≤ (4434808418289/10000000000000 : ℝ)^1619
        have hw : |(5391600351/10000000000 : ℝ)|=(5391600351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_2 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642272971/5000000000 : ℝ)*x 0 + (1347900031/2500000000 : ℝ)*x 1 + (-410998931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642272971/5000000000 : ℝ)^2131 ≤ (43192700011607/100000000000000 : ℝ)^1619 := by
    have hnat : (2642272971 : ℕ)^2131*100000000000000^1619 ≤ 43192700011607^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642272971 5000000000 43192700011607 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347900031/2500000000 : ℝ)^2131 ≤ (44348081725243/100000000000000 : ℝ)^1619 := by
    have hnat : (1347900031 : ℕ)^2131*100000000000000^1619 ≤ 44348081725243^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347900031 2500000000 44348081725243 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410998931/2000000000 : ℝ)^2131 ≤ (1245921824697/10000000000000 : ℝ)^1619 := by
    have hnat : (410998931 : ℕ)^2131*10000000000000^1619 ≤ 1245921824697^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410998931 2000000000 1245921824697 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642272971/5000000000 : ℝ), (1347900031/2500000000 : ℝ), (-410998931/2000000000 : ℝ)] ![(43192700011607/100000000000000 : ℝ), (44348081725243/100000000000000 : ℝ), (1245921824697/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642272971/5000000000 : ℝ)|^2131 ≤ (43192700011607/100000000000000 : ℝ)^1619
        have hw : |(2642272971/5000000000 : ℝ)|=(2642272971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347900031/2500000000 : ℝ)|^2131 ≤ (44348081725243/100000000000000 : ℝ)^1619
        have hw : |(1347900031/2500000000 : ℝ)|=(1347900031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410998931/2000000000 : ℝ)|^2131 ≤ (1245921824697/10000000000000 : ℝ)^1619
        have hw : |(-410998931/2000000000 : ℝ)|=(410998931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_3 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4486358301/10000000000 : ℝ)*x 0 + (4266588687/10000000000 : ℝ)*x 1 + (4266588763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486358301/10000000000 : ℝ)^2131 ≤ (34818278930833/100000000000000 : ℝ)^1619 := by
    have hnat : (4486358301 : ℕ)^2131*100000000000000^1619 ≤ 34818278930833^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486358301 10000000000 34818278930833 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4266588687/10000000000 : ℝ)^2131 ≤ (32590860145143/100000000000000 : ℝ)^1619 := by
    have hnat : (4266588687 : ℕ)^2131*100000000000000^1619 ≤ 32590860145143^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266588687 10000000000 32590860145143 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4266588763/10000000000 : ℝ)^2131 ≤ (3259086090927/10000000000000 : ℝ)^1619 := by
    have hnat : (4266588763 : ℕ)^2131*10000000000000^1619 ≤ 3259086090927^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266588763 10000000000 3259086090927 10000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486358301/10000000000 : ℝ), (4266588687/10000000000 : ℝ), (4266588763/10000000000 : ℝ)] ![(34818278930833/100000000000000 : ℝ), (32590860145143/100000000000000 : ℝ), (3259086090927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486358301/10000000000 : ℝ)|^2131 ≤ (34818278930833/100000000000000 : ℝ)^1619
        have hw : |(4486358301/10000000000 : ℝ)|=(4486358301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4266588687/10000000000 : ℝ)|^2131 ≤ (32590860145143/100000000000000 : ℝ)^1619
        have hw : |(4266588687/10000000000 : ℝ)|=(4266588687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4266588763/10000000000 : ℝ)|^2131 ≤ (3259086090927/10000000000000 : ℝ)^1619
        have hw : |(4266588763/10000000000 : ℝ)|=(4266588763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_4 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-563077311/2500000000 : ℝ)*x 0 + (1052792141/2000000000 : ℝ)*x 1 + (42111689/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563077311/2500000000 : ℝ)^2131 ≤ (7028621125047/50000000000000 : ℝ)^1619 := by
    have hnat : (563077311 : ℕ)^2131*50000000000000^1619 ≤ 7028621125047^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563077311 2500000000 7028621125047 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052792141/2000000000 : ℝ)^2131 ≤ (21485688307667/50000000000000 : ℝ)^1619 := by
    have hnat : (1052792141 : ℕ)^2131*50000000000000^1619 ≤ 21485688307667^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052792141 2000000000 21485688307667 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42111689/80000000 : ℝ)^2131 ≤ (42971381128201/100000000000000 : ℝ)^1619 := by
    have hnat : (42111689 : ℕ)^2131*100000000000000^1619 ≤ 42971381128201^1619*80000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42111689 80000000 42971381128201 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563077311/2500000000 : ℝ), (1052792141/2000000000 : ℝ), (42111689/80000000 : ℝ)] ![(7028621125047/50000000000000 : ℝ), (21485688307667/50000000000000 : ℝ), (42971381128201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563077311/2500000000 : ℝ)|^2131 ≤ (7028621125047/50000000000000 : ℝ)^1619
        have hw : |(-563077311/2500000000 : ℝ)|=(563077311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052792141/2000000000 : ℝ)|^2131 ≤ (21485688307667/50000000000000 : ℝ)^1619
        have hw : |(1052792141/2000000000 : ℝ)|=(1052792141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42111689/80000000 : ℝ)|^2131 ≤ (42971381128201/100000000000000 : ℝ)^1619
        have hw : |(42111689/80000000 : ℝ)|=(42111689/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_5 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5374350307/10000000000 : ℝ)*x 0 + (-526480081/2500000000 : ℝ)*x 1 + (2631980497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374350307/10000000000 : ℝ)^2131 ≤ (345011083479/781250000000 : ℝ)^1619 := by
    have hnat : (5374350307 : ℕ)^2131*781250000000^1619 ≤ 345011083479^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374350307 10000000000 345011083479 781250000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526480081/2500000000 : ℝ)^2131 ≤ (6433600788991/50000000000000 : ℝ)^1619 := by
    have hnat : (526480081 : ℕ)^2131*50000000000000^1619 ≤ 6433600788991^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526480081 2500000000 6433600788991 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631980497/5000000000 : ℝ)^2131 ≤ (42971379720617/100000000000000 : ℝ)^1619 := by
    have hnat : (2631980497 : ℕ)^2131*100000000000000^1619 ≤ 42971379720617^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631980497 5000000000 42971379720617 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374350307/10000000000 : ℝ), (-526480081/2500000000 : ℝ), (2631980497/5000000000 : ℝ)] ![(345011083479/781250000000 : ℝ), (6433600788991/50000000000000 : ℝ), (42971379720617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374350307/10000000000 : ℝ)|^2131 ≤ (345011083479/781250000000 : ℝ)^1619
        have hw : |(5374350307/10000000000 : ℝ)|=(5374350307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-526480081/2500000000 : ℝ)|^2131 ≤ (6433600788991/50000000000000 : ℝ)^1619
        have hw : |(-526480081/2500000000 : ℝ)|=(526480081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631980497/5000000000 : ℝ)|^2131 ≤ (42971379720617/100000000000000 : ℝ)^1619
        have hw : |(2631980497/5000000000 : ℝ)|=(2631980497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_6 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074870063/2000000000 : ℝ)*x 0 + (5263960679/10000000000 : ℝ)*x 1 + (-1052960367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074870063/2000000000 : ℝ)^2131 ≤ (22080709385919/50000000000000 : ℝ)^1619 := by
    have hnat : (1074870063 : ℕ)^2131*50000000000000^1619 ≤ 22080709385919^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074870063 2000000000 22080709385919 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263960679/10000000000 : ℝ)^2131 ≤ (21485688167983/50000000000000 : ℝ)^1619 := by
    have hnat : (5263960679 : ℕ)^2131*50000000000000^1619 ≤ 21485688167983^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263960679 10000000000 21485688167983 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052960367/5000000000 : ℝ)^2131 ≤ (6433602437657/50000000000000 : ℝ)^1619 := by
    have hnat : (1052960367 : ℕ)^2131*50000000000000^1619 ≤ 6433602437657^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052960367 5000000000 6433602437657 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074870063/2000000000 : ℝ), (5263960679/10000000000 : ℝ), (-1052960367/5000000000 : ℝ)] ![(22080709385919/50000000000000 : ℝ), (21485688167983/50000000000000 : ℝ), (6433602437657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074870063/2000000000 : ℝ)|^2131 ≤ (22080709385919/50000000000000 : ℝ)^1619
        have hw : |(1074870063/2000000000 : ℝ)|=(1074870063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263960679/10000000000 : ℝ)|^2131 ≤ (21485688167983/50000000000000 : ℝ)^1619
        have hw : |(5263960679/10000000000 : ℝ)|=(5263960679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052960367/5000000000 : ℝ)|^2131 ≤ (6433602437657/50000000000000 : ℝ)^1619
        have hw : |(-1052960367/5000000000 : ℝ)|=(1052960367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_7 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1046789573/2500000000 : ℝ)*x 0 + (88322677/200000000 : ℝ)*x 1 + (2208066809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046789573/2500000000 : ℝ)^2131 ≤ (31794604452361/100000000000000 : ℝ)^1619 := by
    have hnat : (1046789573 : ℕ)^2131*100000000000000^1619 ≤ 31794604452361^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046789573 2500000000 31794604452361 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88322677/200000000 : ℝ)^2131 ≤ (852567473563/2500000000000 : ℝ)^1619 := by
    have hnat : (88322677 : ℕ)^2131*2500000000000^1619 ≤ 852567473563^1619*200000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88322677 200000000 852567473563 2500000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208066809/5000000000 : ℝ)^2131 ≤ (8525674146093/25000000000000 : ℝ)^1619 := by
    have hnat : (2208066809 : ℕ)^2131*25000000000000^1619 ≤ 8525674146093^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208066809 5000000000 8525674146093 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046789573/2500000000 : ℝ), (88322677/200000000 : ℝ), (2208066809/5000000000 : ℝ)] ![(31794604452361/100000000000000 : ℝ), (852567473563/2500000000000 : ℝ), (8525674146093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046789573/2500000000 : ℝ)|^2131 ≤ (31794604452361/100000000000000 : ℝ)^1619
        have hw : |(1046789573/2500000000 : ℝ)|=(1046789573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88322677/200000000 : ℝ)|^2131 ≤ (852567473563/2500000000000 : ℝ)^1619
        have hw : |(88322677/200000000 : ℝ)|=(88322677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208066809/5000000000 : ℝ)|^2131 ≤ (8525674146093/25000000000000 : ℝ)^1619
        have hw : |(2208066809/5000000000 : ℝ)|=(2208066809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_8 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-545057277/2500000000 : ℝ)*x 0 + (1035256767/2000000000 : ℝ)*x 1 + (1081126963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545057277/2500000000 : ℝ)^2131 ≤ (13468120965991/100000000000000 : ℝ)^1619 := by
    have hnat : (545057277 : ℕ)^2131*100000000000000^1619 ≤ 13468120965991^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545057277 2500000000 13468120965991 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035256767/2000000000 : ℝ)^2131 ≤ (42031786208567/100000000000000 : ℝ)^1619 := by
    have hnat : (1035256767 : ℕ)^2131*100000000000000^1619 ≤ 42031786208567^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035256767 2000000000 42031786208567 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081126963/2000000000 : ℝ)^2131 ≤ (22250046400933/50000000000000 : ℝ)^1619 := by
    have hnat : (1081126963 : ℕ)^2131*50000000000000^1619 ≤ 22250046400933^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081126963 2000000000 22250046400933 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545057277/2500000000 : ℝ), (1035256767/2000000000 : ℝ), (1081126963/2000000000 : ℝ)] ![(13468120965991/100000000000000 : ℝ), (42031786208567/100000000000000 : ℝ), (22250046400933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545057277/2500000000 : ℝ)|^2131 ≤ (13468120965991/100000000000000 : ℝ)^1619
        have hw : |(-545057277/2500000000 : ℝ)|=(545057277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035256767/2000000000 : ℝ)|^2131 ≤ (42031786208567/100000000000000 : ℝ)^1619
        have hw : |(1035256767/2000000000 : ℝ)|=(1035256767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081126963/2000000000 : ℝ)|^2131 ≤ (22250046400933/50000000000000 : ℝ)^1619
        have hw : |(1081126963/2000000000 : ℝ)|=(1081126963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_9 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5274665379/10000000000 : ℝ)*x 0 + (-128078737/625000000 : ℝ)*x 1 + (5405634809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274665379/10000000000 : ℝ)^2131 ≤ (43086434460713/100000000000000 : ℝ)^1619 := by
    have hnat : (5274665379 : ℕ)^2131*100000000000000^1619 ≤ 43086434460713^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274665379 10000000000 43086434460713 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128078737/625000000 : ℝ)^2131 ≤ (12413472793269/100000000000000 : ℝ)^1619 := by
    have hnat : (128078737 : ℕ)^2131*100000000000000^1619 ≤ 12413472793269^1619*625000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128078737 625000000 12413472793269 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405634809/10000000000 : ℝ)^2131 ≤ (44500092736853/100000000000000 : ℝ)^1619 := by
    have hnat : (5405634809 : ℕ)^2131*100000000000000^1619 ≤ 44500092736853^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405634809 10000000000 44500092736853 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274665379/10000000000 : ℝ), (-128078737/625000000 : ℝ), (5405634809/10000000000 : ℝ)] ![(43086434460713/100000000000000 : ℝ), (12413472793269/100000000000000 : ℝ), (44500092736853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274665379/10000000000 : ℝ)|^2131 ≤ (43086434460713/100000000000000 : ℝ)^1619
        have hw : |(5274665379/10000000000 : ℝ)|=(5274665379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128078737/625000000 : ℝ)|^2131 ≤ (12413472793269/100000000000000 : ℝ)^1619
        have hw : |(-128078737/625000000 : ℝ)|=(128078737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405634809/10000000000 : ℝ)|^2131 ≤ (44500092736853/100000000000000 : ℝ)^1619
        have hw : |(5405634809/10000000000 : ℝ)|=(5405634809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_10 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (527466539/1000000000 : ℝ)*x 0 + (1351408729/2500000000 : ℝ)*x 1 + (-2049259631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527466539/1000000000 : ℝ)^2131 ≤ (43086434578983/100000000000000 : ℝ)^1619 := by
    have hnat : (527466539 : ℕ)^2131*100000000000000^1619 ≤ 43086434578983^1619*1000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527466539 1000000000 43086434578983 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351408729/2500000000 : ℝ)^2131 ≤ (695313967129/1562500000000 : ℝ)^1619 := by
    have hnat : (1351408729 : ℕ)^2131*1562500000000^1619 ≤ 695313967129^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351408729 2500000000 695313967129 1562500000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049259631/10000000000 : ℝ)^2131 ≤ (12413471509583/100000000000000 : ℝ)^1619 := by
    have hnat : (2049259631 : ℕ)^2131*100000000000000^1619 ≤ 12413471509583^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049259631 10000000000 12413471509583 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527466539/1000000000 : ℝ), (1351408729/2500000000 : ℝ), (-2049259631/10000000000 : ℝ)] ![(43086434578983/100000000000000 : ℝ), (695313967129/1562500000000 : ℝ), (12413471509583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527466539/1000000000 : ℝ)|^2131 ≤ (43086434578983/100000000000000 : ℝ)^1619
        have hw : |(527466539/1000000000 : ℝ)|=(527466539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351408729/2500000000 : ℝ)|^2131 ≤ (695313967129/1562500000000 : ℝ)^1619
        have hw : |(1351408729/2500000000 : ℝ)|=(1351408729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049259631/10000000000 : ℝ)|^2131 ≤ (12413471509583/100000000000000 : ℝ)^1619
        have hw : |(-2049259631/10000000000 : ℝ)|=(2049259631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_11 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (903739457/2000000000 : ℝ)*x 0 + (1062532897/2500000000 : ℝ)*x 1 + (2125065813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903739457/2000000000 : ℝ)^2131 ≤ (1405960254879/4000000000000 : ℝ)^1619 := by
    have hnat : (903739457 : ℕ)^2131*4000000000000^1619 ≤ 1405960254879^1619*2000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903739457 2000000000 1405960254879 4000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062532897/2500000000 : ℝ)^2131 ≤ (6485099323137/20000000000000 : ℝ)^1619 := by
    have hnat : (1062532897 : ℕ)^2131*20000000000000^1619 ≤ 6485099323137^1619*2500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062532897 2500000000 6485099323137 20000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125065813/5000000000 : ℝ)^2131 ≤ (16212748498641/50000000000000 : ℝ)^1619 := by
    have hnat : (2125065813 : ℕ)^2131*50000000000000^1619 ≤ 16212748498641^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125065813 5000000000 16212748498641 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(903739457/2000000000 : ℝ), (1062532897/2500000000 : ℝ), (2125065813/5000000000 : ℝ)] ![(1405960254879/4000000000000 : ℝ), (6485099323137/20000000000000 : ℝ), (16212748498641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(903739457/2000000000 : ℝ)|^2131 ≤ (1405960254879/4000000000000 : ℝ)^1619
        have hw : |(903739457/2000000000 : ℝ)|=(903739457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062532897/2500000000 : ℝ)|^2131 ≤ (6485099323137/20000000000000 : ℝ)^1619
        have hw : |(1062532897/2500000000 : ℝ)|=(1062532897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125065813/5000000000 : ℝ)|^2131 ≤ (16212748498641/50000000000000 : ℝ)^1619
        have hw : |(2125065813/5000000000 : ℝ)|=(2125065813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_12 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-990517257/5000000000 : ℝ)*x 0 + (54769783/100000000 : ℝ)*x 1 + (2626463921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990517257/5000000000 : ℝ)^2131 ≤ (5936192208811/50000000000000 : ℝ)^1619 := by
    have hnat : (990517257 : ℕ)^2131*50000000000000^1619 ≤ 5936192208811^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990517257 5000000000 5936192208811 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54769783/100000000 : ℝ)^2131 ≤ (45274746880657/100000000000000 : ℝ)^1619 := by
    have hnat : (54769783 : ℕ)^2131*100000000000000^1619 ≤ 45274746880657^1619*100000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54769783 100000000 45274746880657 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626463921/5000000000 : ℝ)^2131 ≤ (42852868680161/100000000000000 : ℝ)^1619 := by
    have hnat : (2626463921 : ℕ)^2131*100000000000000^1619 ≤ 42852868680161^1619*5000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626463921 5000000000 42852868680161 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990517257/5000000000 : ℝ), (54769783/100000000 : ℝ), (2626463921/5000000000 : ℝ)] ![(5936192208811/50000000000000 : ℝ), (45274746880657/100000000000000 : ℝ), (42852868680161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990517257/5000000000 : ℝ)|^2131 ≤ (5936192208811/50000000000000 : ℝ)^1619
        have hw : |(-990517257/5000000000 : ℝ)|=(990517257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54769783/100000000 : ℝ)|^2131 ≤ (45274746880657/100000000000000 : ℝ)^1619
        have hw : |(54769783/100000000 : ℝ)|=(54769783/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626463921/5000000000 : ℝ)|^2131 ≤ (42852868680161/100000000000000 : ℝ)^1619
        have hw : |(2626463921/5000000000 : ℝ)|=(2626463921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_13 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269105509/500000000 : ℝ)*x 0 + (-2110216737/10000000000 : ℝ)*x 1 + (5252927801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269105509/500000000 : ℝ)^2131 ≤ (11061341527107/25000000000000 : ℝ)^1619 := by
    have hnat : (269105509 : ℕ)^2131*25000000000000^1619 ≤ 11061341527107^1619*500000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269105509 500000000 11061341527107 25000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110216737/10000000000 : ℝ)^2131 ≤ (12901765642341/100000000000000 : ℝ)^1619 := by
    have hnat : (2110216737 : ℕ)^2131*100000000000000^1619 ≤ 12901765642341^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110216737 10000000000 12901765642341 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252927801/10000000000 : ℝ)^2131 ≤ (42852868239911/100000000000000 : ℝ)^1619 := by
    have hnat : (5252927801 : ℕ)^2131*100000000000000^1619 ≤ 42852868239911^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252927801 10000000000 42852868239911 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269105509/500000000 : ℝ), (-2110216737/10000000000 : ℝ), (5252927801/10000000000 : ℝ)] ![(11061341527107/25000000000000 : ℝ), (12901765642341/100000000000000 : ℝ), (42852868239911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269105509/500000000 : ℝ)|^2131 ≤ (11061341527107/25000000000000 : ℝ)^1619
        have hw : |(269105509/500000000 : ℝ)|=(269105509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110216737/10000000000 : ℝ)|^2131 ≤ (12901765642341/100000000000000 : ℝ)^1619
        have hw : |(-2110216737/10000000000 : ℝ)|=(2110216737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252927801/10000000000 : ℝ)|^2131 ≤ (42852868239911/100000000000000 : ℝ)^1619
        have hw : |(5252927801/10000000000 : ℝ)|=(5252927801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_14 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8409547/15625000 : ℝ)*x 0 + (5252927921/10000000000 : ℝ)*x 1 + (-2110216711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8409547/15625000 : ℝ)^2131 ≤ (44245365026367/100000000000000 : ℝ)^1619 := by
    have hnat : (8409547 : ℕ)^2131*100000000000000^1619 ≤ 44245365026367^1619*15625000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8409547 15625000 44245365026367 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252927921/10000000000 : ℝ)^2131 ≤ (21426434764223/50000000000000 : ℝ)^1619 := by
    have hnat : (5252927921 : ℕ)^2131*50000000000000^1619 ≤ 21426434764223^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252927921 10000000000 21426434764223 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110216711/10000000000 : ℝ)^2131 ≤ (12901765433107/100000000000000 : ℝ)^1619 := by
    have hnat : (2110216711 : ℕ)^2131*100000000000000^1619 ≤ 12901765433107^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110216711 10000000000 12901765433107 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8409547/15625000 : ℝ), (5252927921/10000000000 : ℝ), (-2110216711/10000000000 : ℝ)] ![(44245365026367/100000000000000 : ℝ), (21426434764223/50000000000000 : ℝ), (12901765433107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8409547/15625000 : ℝ)|^2131 ≤ (44245365026367/100000000000000 : ℝ)^1619
        have hw : |(8409547/15625000 : ℝ)|=(8409547/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252927921/10000000000 : ℝ)|^2131 ≤ (21426434764223/50000000000000 : ℝ)^1619
        have hw : |(5252927921/10000000000 : ℝ)|=(5252927921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110216711/10000000000 : ℝ)|^2131 ≤ (12901765433107/100000000000000 : ℝ)^1619
        have hw : |(-2110216711/10000000000 : ℝ)|=(2110216711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1302_box_15 (p : ℝ) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ)) (x : Fin 3 → ℝ) :
    (520106071/1250000000 : ℝ)*x 0 + (442905003/1000000000 : ℝ)*x 1 + (4429050199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520106071/1250000000 : ℝ)^2131 ≤ (31531907755549/100000000000000 : ℝ)^1619 := by
    have hnat : (520106071 : ℕ)^2131*100000000000000^1619 ≤ 31531907755549^1619*1250000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520106071 1250000000 31531907755549 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442905003/1000000000 : ℝ)^2131 ≤ (17117022627027/50000000000000 : ℝ)^1619 := by
    have hnat : (442905003 : ℕ)^2131*50000000000000^1619 ≤ 17117022627027^1619*1000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442905003 1000000000 17117022627027 50000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429050199/10000000000 : ℝ)^2131 ≤ (34234046973431/100000000000000 : ℝ)^1619 := by
    have hnat : (4429050199 : ℕ)^2131*100000000000000^1619 ≤ 34234046973431^1619*10000000000^2131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429050199 10000000000 34234046973431 100000000000000 2131 1619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2131/512 : ℝ)) 2131 1619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520106071/1250000000 : ℝ), (442905003/1000000000 : ℝ), (4429050199/10000000000 : ℝ)] ![(31531907755549/100000000000000 : ℝ), (17117022627027/50000000000000 : ℝ), (34234046973431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520106071/1250000000 : ℝ)|^2131 ≤ (31531907755549/100000000000000 : ℝ)^1619
        have hw : |(520106071/1250000000 : ℝ)|=(520106071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442905003/1000000000 : ℝ)|^2131 ≤ (17117022627027/50000000000000 : ℝ)^1619
        have hw : |(442905003/1000000000 : ℝ)|=(442905003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4429050199/10000000000 : ℝ)|^2131 ≤ (34234046973431/100000000000000 : ℝ)^1619
        have hw : |(4429050199/10000000000 : ℝ)|=(4429050199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1302_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11053/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31421/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3679/6250 : ℝ) ∧ (79717/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16839/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11053/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11053/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11053/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11053/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11053/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11053/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11053/100000 : ℝ) ^ (4261/1024 : ℝ) ≤ (10466318574133579/100000000000000000000 : ℝ) := by
    have hpowers : (11053/100000 : ℝ)^4261 ≤ (10466318574133579/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11053 : ℕ)^4261*100000000000000000000^1024 ≤ 10466318574133579^1024*100000^4261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11053 100000 10466318574133579 100000000000000000000 4261 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11053/100000 : ℝ)) (X := (10466318574133579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (4261/1024 : ℝ) ≤ (17040539678674449/50000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^4261 ≤ (17040539678674449/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14679 : ℕ)^4261*50000000000000000000^1024 ≤ 17040539678674449^1024*100000^4261 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 17040539678674449 50000000000000000000 4261 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (17040539678674449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010466318574133579/50000000000000000000 : ℝ) ≤ (2500125752853423/2500000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (50010466318574133579/50000000000000000000 : ℝ)^1024 ≤ (2500125752853423/2500000000000000 : ℝ)^4261 := by
      have hnat : (50010466318574133579 : ℕ)^1024*2500000000000000^4261 ≤ 2500125752853423^4261*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010466318574133579 50000000000000000000 2500125752853423 2500000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500125752853423/2500000000000000 : ℝ)) (X := (50010466318574133579/50000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044547397931482477/100000000000000000000 : ℝ) ≤ (1250133797285757/1250000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (100044547397931482477/100000000000000000000 : ℝ)^1024 ≤ (1250133797285757/1250000000000000 : ℝ)^4261 := by
      have hnat : (100044547397931482477 : ℕ)^1024*1250000000000000^4261 ≤ 1250133797285757^4261*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044547397931482477 100000000000000000000 1250133797285757 1250000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250133797285757/1250000000000000 : ℝ)) (X := (100044547397931482477/100000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017040539678674449/25000000000000000000 : ℝ) ≤ (500081887257921/500000000000000 : ℝ) ^ (4261/1024 : ℝ) := by
    have hpowers : (25017040539678674449/25000000000000000000 : ℝ)^1024 ≤ (500081887257921/500000000000000 : ℝ)^4261 := by
      have hnat : (25017040539678674449 : ℕ)^1024*500000000000000^4261 ≤ 500081887257921^4261*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017040539678674449 25000000000000000000 500081887257921 500000000000000 1024 4261 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500081887257921/500000000000000 : ℝ)) (X := (25017040539678674449/25000000000000000000 : ℝ)) (by norm_num) 4261 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10466318574133579/100000000000000000000 : ℝ) ≤ ((161827150479042717/161875000000000000 : ℝ)+2*(141841718091/90650000000000 : ℝ)*(11053/100000 : ℝ))^(4261/1024 : ℝ) := by
    rw [show (161827150479042717/161875000000000000 : ℝ)+2*(141841718091/90650000000000 : ℝ)*(11053/100000 : ℝ)=(2500125752853423/2500000000000000 : ℝ) by norm_num, show 1+2*(10466318574133579/100000000000000000000 : ℝ)=(50010466318574133579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17040539678674449/50000000000000000000 : ℝ)+(10466318574133579/100000000000000000000 : ℝ) ≤ ((161827150479042717/161875000000000000 : ℝ)+(141841718091/90650000000000 : ℝ)*((14679/100000 : ℝ)+(11053/100000 : ℝ)))^(4261/1024 : ℝ) := by
    rw [show (161827150479042717/161875000000000000 : ℝ)+(141841718091/90650000000000 : ℝ)*((14679/100000 : ℝ)+(11053/100000 : ℝ))=(1250133797285757/1250000000000000 : ℝ) by norm_num, show 1+(17040539678674449/50000000000000000000 : ℝ)+(10466318574133579/100000000000000000000 : ℝ)=(100044547397931482477/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17040539678674449/50000000000000000000 : ℝ) ≤ ((161827150479042717/161875000000000000 : ℝ)+2*(141841718091/90650000000000 : ℝ)*(14679/100000 : ℝ))^(4261/1024 : ℝ) := by
    rw [show (161827150479042717/161875000000000000 : ℝ)+2*(141841718091/90650000000000 : ℝ)*(14679/100000 : ℝ)=(500081887257921/500000000000000 : ℝ) by norm_num, show 1+2*(17040539678674449/50000000000000000000 : ℝ)=(25017040539678674449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (161827150479042717/161875000000000000 : ℝ)*(X 1 0+X 2 0)+(141841718091/90650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11053/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (161827150479042717/161875000000000000 : ℝ)) (alpha := (141841718091/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (161827150479042717/161875000000000000 : ℝ)*(X 0 1+X 2 1)+(141841718091/90650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11053/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (161827150479042717/161875000000000000 : ℝ)) (alpha := (141841718091/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (161827150479042717/161875000000000000 : ℝ)*(X 0 2+X 1 2)+(141841718091/90650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4261/1024 : ℝ)) (lo := (11053/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (161827150479042717/161875000000000000 : ℝ)) (alpha := (141841718091/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1908536419/10000000000 : ℝ)*X 0 0+(5391600089/10000000000 : ℝ)*X 0 1+(2695800093/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660568213/1250000000 : ℝ)*X 1 0+(-513748667/2500000000 : ℝ)*X 1 1+(5391600351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642272971/5000000000 : ℝ)*X 2 0+(1347900031/2500000000 : ℝ)*X 2 1+(-410998931/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4486358301/10000000000 : ℝ)*X 0 0+(4266588687/10000000000 : ℝ)*X 0 1+(4266588763/10000000000 : ℝ)*X 0 2+(4486358301/10000000000 : ℝ)*X 1 0+(4266588687/10000000000 : ℝ)*X 1 1+(4266588763/10000000000 : ℝ)*X 1 2+(4486358301/10000000000 : ℝ)*X 2 0+(4266588687/10000000000 : ℝ)*X 2 1+(4266588763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-563077311/2500000000 : ℝ)*X 0 0+(1052792141/2000000000 : ℝ)*X 0 1+(42111689/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374350307/10000000000 : ℝ)*X 1 0+(-526480081/2500000000 : ℝ)*X 1 1+(2631980497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074870063/2000000000 : ℝ)*X 2 0+(5263960679/10000000000 : ℝ)*X 2 1+(-1052960367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1046789573/2500000000 : ℝ)*X 0 0+(88322677/200000000 : ℝ)*X 0 1+(2208066809/5000000000 : ℝ)*X 0 2+(1046789573/2500000000 : ℝ)*X 1 0+(88322677/200000000 : ℝ)*X 1 1+(2208066809/5000000000 : ℝ)*X 1 2+(1046789573/2500000000 : ℝ)*X 2 0+(88322677/200000000 : ℝ)*X 2 1+(2208066809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-545057277/2500000000 : ℝ)*X 0 0+(1035256767/2000000000 : ℝ)*X 0 1+(1081126963/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274665379/10000000000 : ℝ)*X 1 0+(-128078737/625000000 : ℝ)*X 1 1+(5405634809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((527466539/1000000000 : ℝ)*X 2 0+(1351408729/2500000000 : ℝ)*X 2 1+(-2049259631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((903739457/2000000000 : ℝ)*X 0 0+(1062532897/2500000000 : ℝ)*X 0 1+(2125065813/5000000000 : ℝ)*X 0 2+(903739457/2000000000 : ℝ)*X 1 0+(1062532897/2500000000 : ℝ)*X 1 1+(2125065813/5000000000 : ℝ)*X 1 2+(903739457/2000000000 : ℝ)*X 2 0+(1062532897/2500000000 : ℝ)*X 2 1+(2125065813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-990517257/5000000000 : ℝ)*X 0 0+(54769783/100000000 : ℝ)*X 0 1+(2626463921/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((269105509/500000000 : ℝ)*X 1 0+(-2110216737/10000000000 : ℝ)*X 1 1+(5252927801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((8409547/15625000 : ℝ)*X 2 0+(5252927921/10000000000 : ℝ)*X 2 1+(-2110216711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((520106071/1250000000 : ℝ)*X 0 0+(442905003/1000000000 : ℝ)*X 0 1+(4429050199/10000000000 : ℝ)*X 0 2+(520106071/1250000000 : ℝ)*X 1 0+(442905003/1000000000 : ℝ)*X 1 1+(4429050199/10000000000 : ℝ)*X 1 2+(520106071/1250000000 : ℝ)*X 2 0+(442905003/1000000000 : ℝ)*X 2 1+(4429050199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1302_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31421/50000 : ℝ) ≤ (-363290040278340740562950749167/578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144568357/100000000000000 : ℝ)*(upper1) + (163346603/100000000000000 : ℝ)*(lower4) + (34808667/100000000000000 : ℝ)*(upper5) + (1437743333236847/50000000000000 : ℝ)*(major0) + (1437743333236847/50000000000000 : ℝ)*(major1) + (1437743333236847/50000000000000 : ℝ)*(major2) + (10830900697/100000000000000 : ℝ)*(sp2) + (5248178421/100000000000000 : ℝ)*(sp3) + (243400638658771/6250000000000 : ℝ)*(sp4) + (3894325427523691/100000000000000 : ℝ)*(sp5) + (1947201884034933/50000000000000 : ℝ)*(sp6) + (1877499938571199/100000000000000 : ℝ)*(sp7) + (4380430227/100000000000000 : ℝ)*(sp12) + (11146430859/12500000000000 : ℝ)*(sp13) + (93875259337481/5000000000000 : ℝ)*(f.failure) + (973603649742641/25000000000000 : ℝ)*(f.sum) + (409619702603/185000000000000000000000000 : ℝ)*base66 + (1127806833633993/1156250000000000000000000000000 : ℝ)*base68 + (5451037155928507/1156250000000000000000000000000 : ℝ)*base69 + (10985467570959757/1156250000000000000000000000000 : ℝ)*base71 + (1033787995073/185000000000000000000000000 : ℝ)*base74 + (4915601840178507/1156250000000000000000000000000 : ℝ)*base75 + (13622354355991007/1156250000000000000000000000000 : ℝ)*base77 + (7866529569678507/1156250000000000000000000000000 : ℝ)*base79 + (113719630759/92500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1526021/500000000000000000000 : ℝ)*base90 + (1526021/500000000000000000000 : ℝ)*base92 + (1526021/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3679/6250 : ℝ) ≤ (1042238354260067767819743409047/1770507812500000000000000000000 : ℝ) := by norm_num
    linear_combination (2645929/25000000000000 : ℝ)*(lower1) + (95267/400000000000 : ℝ)*(lower3) + (35477121/100000000000000 : ℝ)*(upper4) + (18494037/100000000000000 : ℝ)*(upper5) + (367855204011233/12500000000000 : ℝ)*(major0) + (367855204011233/12500000000000 : ℝ)*(major1) + (367855204011233/12500000000000 : ℝ)*(major2) + (1972288734004211/50000000000000 : ℝ)*(sp0) + (3944571332082397/100000000000000 : ℝ)*(sp1) + (246535882982921/6250000000000 : ℝ)*(sp2) + (1921483368535043/100000000000000 : ℝ)*(sp3) + (3067963013/50000000000000 : ℝ)*(sp5) + (21629659/10000000000000 : ℝ)*(sp7) + (1670140843/50000000000000 : ℝ)*(sp10) + (1921483584831633/100000000000000 : ℝ)*(f.failure) + (1972288734004211/50000000000000 : ℝ)*(f.sum) + (36197451037077/9065000000000000000000000000 : ℝ)*base66 + (171812829544913979/28328125000000000000000000000000 : ℝ)*base67 + (2618754587251382729/28328125000000000000000000000000 : ℝ)*base69 + (71000251821054771/28328125000000000000000000000000 : ℝ)*base72 + (28431220927117/9065000000000000000000000000 : ℝ)*base74 + (1662702882225011677/14164062500000000000000000000000 : ℝ)*base75 + (87467551888851479/28328125000000000000000000000000 : ℝ)*base77 + (169979600940757729/28328125000000000000000000000000 : ℝ)*base79 + (1615556821130853/9065000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (75471853/10000000000000000000000 : ℝ)*base90 + (75471853/10000000000000000000000 : ℝ)*base92 + (75471853/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79717/100000 : ℝ) ≤ (45166052496708456017045547045519/56656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24092321/50000000000000 : ℝ)*(upper0) + (1677029/25000000000000 : ℝ)*(upper1) + (68199421/100000000000000 : ℝ)*(upper4) + (3256489041949139/100000000000000 : ℝ)*(major0) + (3256489041949139/100000000000000 : ℝ)*(major1) + (3256489041949139/100000000000000 : ℝ)*(major2) + (649185161/10000000000000 : ℝ)*(sp1) + (17665368969/25000000000000 : ℝ)*(sp2) + (29844991721/100000000000000 : ℝ)*(sp3) + (354259443/100000000000000 : ℝ)*(sp4) + (2180064849320017/50000000000000 : ℝ)*(sp8) + (4360123561047867/100000000000000 : ℝ)*(sp9) + (2180029695711801/50000000000000 : ℝ)*(sp10) + (1063122517531067/50000000000000 : ℝ)*(sp11) + (1063137440026927/50000000000000 : ℝ)*(f.failure) + (4360130052899477/100000000000000 : ℝ)*(f.sum) + (6518392280243/9065000000000000000000000000 : ℝ)*base65 + (2037253769667292859/113312500000000000000000000000000 : ℝ)*base68 + (1438955981472542859/113312500000000000000000000000000 : ℝ)*base70 + (813209700071042859/113312500000000000000000000000000 : ℝ)*base72 + (368256251976077/9065000000000000000000000000 : ℝ)*base74 + (1827275701220292859/113312500000000000000000000000000 : ℝ)*base76 + (1820280202533980359/113312500000000000000000000000000 : ℝ)*base78 + (5683316694064980359/113312500000000000000000000000000 : ℝ)*base80 + (5554337716427/9065000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5502893/5000000000000000000000 : ℝ)*base89 + (5502893/5000000000000000000000 : ℝ)*base91 + (5502893/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-16839/20000 : ℝ) ≤ (-93164289861846694795266296967/110656738281250000000000000000 : ℝ) := by norm_num
    linear_combination (2492787/20000000000000 : ℝ)*(lower0) + (18169767/50000000000000 : ℝ)*(lower1) + (1679109/20000000000000 : ℝ)*(lower3) + (16341323/100000000000000 : ℝ)*(lower4) + (823125972841631/25000000000000 : ℝ)*(major0) + (823125972841631/25000000000000 : ℝ)*(major1) + (823125972841631/25000000000000 : ℝ)*(major2) + (2095650979/5000000000000 : ℝ)*(sp5) + (5454388731/100000000000000 : ℝ)*(sp6) + (5875066309/50000000000000 : ℝ)*(sp7) + (4463281606578313/100000000000000 : ℝ)*(sp12) + (4463239693558733/100000000000000 : ℝ)*(sp13) + (2231638076094791/50000000000000 : ℝ)*(sp14) + (1074889238430213/50000000000000 : ℝ)*(sp15) + (537447556748261/25000000000000 : ℝ)*(f.failure) + (4463281606578313/100000000000000 : ℝ)*(f.sum) + (3150084731569/4532500000000000000000000000 : ℝ)*base65 + (492764167083984989/28328125000000000000000000000000 : ℝ)*base67 + (262129965058484989/28328125000000000000000000000000 : ℝ)*base69 + (407238400709422489/28328125000000000000000000000000 : ℝ)*base71 + (38031926414333/9065000000000000000000000000 : ℝ)*base73 + (154163620826187807/14164062500000000000000000000000 : ℝ)*base75 + (76609793752648591/7082031250000000000000000000000 : ℝ)*base77 + (232413209316031557/14164062500000000000000000000000 : ℝ)*base79 + (2170525461931/4532500000000000000000000000 : ℝ)*base82 + (37702001/2500000000000000000000 : ℝ)*base90 + (37702001/2500000000000000000000 : ℝ)*base92 + (37702001/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1302_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11053/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31421/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3679/6250 : ℝ) else (79717/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16839/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1302_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1302_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31421/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3679/6250 : ℝ) else (79717/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16839/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1302_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1302_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1302_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4261/1024 : ℝ) ≤ p) (hpb : p ≤ (2131/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153154659/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31421/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3679/6250 : ℝ) else (79717/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16839/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1302_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
