-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1649_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:36.603191+00:00
-- url     : https://prove2.me/submissions/594ac70f-8f7e-491b-b736-bff34553b6ed

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
theorem support_rectangle_w1649_s3_0 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1610792779/10000000000 : ℝ)*x 0 + (1089580861/2000000000 : ℝ)*x 1 + (323986061/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1610792779/10000000000 : ℝ)^4915 ≤ (4981099102607/50000000000000 : ℝ)^3891 := by
    have hnat : (1610792779 : ℕ)^4915*50000000000000^3891 ≤ 4981099102607^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1610792779 10000000000 4981099102607 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089580861/2000000000 : ℝ)^4915 ≤ (46431488364473/100000000000000 : ℝ)^3891 := by
    have hnat : (1089580861 : ℕ)^4915*100000000000000^3891 ≤ 46431488364473^3891*2000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089580861 2000000000 46431488364473 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323986061/625000000 : ℝ)^4915 ≤ (10901578352399/25000000000000 : ℝ)^3891 := by
    have hnat : (323986061 : ℕ)^4915*25000000000000^3891 ≤ 10901578352399^3891*625000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323986061 625000000 10901578352399 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1610792779/10000000000 : ℝ), (1089580861/2000000000 : ℝ), (323986061/625000000 : ℝ)] ![(4981099102607/50000000000000 : ℝ), (46431488364473/100000000000000 : ℝ), (10901578352399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1610792779/10000000000 : ℝ)|^4915 ≤ (4981099102607/50000000000000 : ℝ)^3891
        have hw : |(-1610792779/10000000000 : ℝ)|=(1610792779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089580861/2000000000 : ℝ)|^4915 ≤ (46431488364473/100000000000000 : ℝ)^3891
        have hw : |(1089580861/2000000000 : ℝ)|=(1089580861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323986061/625000000 : ℝ)|^4915 ≤ (10901578352399/25000000000000 : ℝ)^3891
        have hw : |(323986061/625000000 : ℝ)|=(323986061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_1 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347914321/10000000000 : ℝ)*x 0 + (-1746770273/10000000000 : ℝ)*x 1 + (5183777001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347914321/10000000000 : ℝ)^4915 ≤ (1133940749489/2500000000000 : ℝ)^3891 := by
    have hnat : (5347914321 : ℕ)^4915*2500000000000^3891 ≤ 1133940749489^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347914321 10000000000 1133940749489 2500000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1746770273/10000000000 : ℝ)^4915 ≤ (11036056339327/100000000000000 : ℝ)^3891 := by
    have hnat : (1746770273 : ℕ)^4915*100000000000000^3891 ≤ 11036056339327^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746770273 10000000000 11036056339327 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183777001/10000000000 : ℝ)^4915 ≤ (43606313675243/100000000000000 : ℝ)^3891 := by
    have hnat : (5183777001 : ℕ)^4915*100000000000000^3891 ≤ 43606313675243^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183777001 10000000000 43606313675243 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347914321/10000000000 : ℝ), (-1746770273/10000000000 : ℝ), (5183777001/10000000000 : ℝ)] ![(1133940749489/2500000000000 : ℝ), (11036056339327/100000000000000 : ℝ), (43606313675243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347914321/10000000000 : ℝ)|^4915 ≤ (1133940749489/2500000000000 : ℝ)^3891
        have hw : |(5347914321/10000000000 : ℝ)|=(5347914321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1746770273/10000000000 : ℝ)|^4915 ≤ (11036056339327/100000000000000 : ℝ)^3891
        have hw : |(-1746770273/10000000000 : ℝ)|=(1746770273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183777001/10000000000 : ℝ)|^4915 ≤ (43606313675243/100000000000000 : ℝ)^3891
        have hw : |(5183777001/10000000000 : ℝ)|=(5183777001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_2 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534791429/1000000000 : ℝ)*x 0 + (5183776997/10000000000 : ℝ)*x 1 + (-873385159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534791429/1000000000 : ℝ)^4915 ≤ (11339407411861/25000000000000 : ℝ)^3891 := by
    have hnat : (534791429 : ℕ)^4915*25000000000000^3891 ≤ 11339407411861^3891*1000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534791429 1000000000 11339407411861 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183776997/10000000000 : ℝ)^4915 ≤ (2180315681637/5000000000000 : ℝ)^3891 := by
    have hnat : (5183776997 : ℕ)^4915*5000000000000^3891 ≤ 2180315681637^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183776997 10000000000 2180315681637 5000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873385159/5000000000 : ℝ)^4915 ≤ (5518028349229/50000000000000 : ℝ)^3891 := by
    have hnat : (873385159 : ℕ)^4915*50000000000000^3891 ≤ 5518028349229^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873385159 5000000000 5518028349229 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534791429/1000000000 : ℝ), (5183776997/10000000000 : ℝ), (-873385159/5000000000 : ℝ)] ![(11339407411861/25000000000000 : ℝ), (2180315681637/5000000000000 : ℝ), (5518028349229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534791429/1000000000 : ℝ)|^4915 ≤ (11339407411861/25000000000000 : ℝ)^3891
        have hw : |(534791429/1000000000 : ℝ)|=(534791429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183776997/10000000000 : ℝ)|^4915 ≤ (2180315681637/5000000000000 : ℝ)^3891
        have hw : |(5183776997/10000000000 : ℝ)|=(5183776997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-873385159/5000000000 : ℝ)|^4915 ≤ (5518028349229/50000000000000 : ℝ)^3891
        have hw : |(-873385159/5000000000 : ℝ)|=(873385159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_3 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418148381/1000000000 : ℝ)*x 0 + (481293223/1250000000 : ℝ)*x 1 + (90656973/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418148381/1000000000 : ℝ)^4915 ≤ (4155137702143/12500000000000 : ℝ)^3891 := by
    have hnat : (418148381 : ℕ)^4915*12500000000000^3891 ≤ 4155137702143^3891*1000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418148381 1000000000 4155137702143 12500000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481293223/1250000000 : ℝ)^4915 ≤ (29951260834203/100000000000000 : ℝ)^3891 := by
    have hnat : (481293223 : ℕ)^4915*100000000000000^3891 ≤ 29951260834203^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481293223 1250000000 29951260834203 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90656973/200000000 : ℝ)^4915 ≤ (36807637535583/100000000000000 : ℝ)^3891 := by
    have hnat : (90656973 : ℕ)^4915*100000000000000^3891 ≤ 36807637535583^3891*200000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90656973 200000000 36807637535583 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418148381/1000000000 : ℝ), (481293223/1250000000 : ℝ), (90656973/200000000 : ℝ)] ![(4155137702143/12500000000000 : ℝ), (29951260834203/100000000000000 : ℝ), (36807637535583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418148381/1000000000 : ℝ)|^4915 ≤ (4155137702143/12500000000000 : ℝ)^3891
        have hw : |(418148381/1000000000 : ℝ)|=(418148381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481293223/1250000000 : ℝ)|^4915 ≤ (29951260834203/100000000000000 : ℝ)^3891
        have hw : |(481293223/1250000000 : ℝ)|=(481293223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90656973/200000000 : ℝ)|^4915 ≤ (36807637535583/100000000000000 : ℝ)^3891
        have hw : |(90656973/200000000 : ℝ)|=(90656973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_4 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201357137/1250000000 : ℝ)*x 0 + (5185776347/10000000000 : ℝ)*x 1 + (2722942021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201357137/1250000000 : ℝ)^4915 ≤ (9962700670261/100000000000000 : ℝ)^3891 := by
    have hnat : (201357137 : ℕ)^4915*100000000000000^3891 ≤ 9962700670261^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201357137 1250000000 9962700670261 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185776347/10000000000 : ℝ)^4915 ≤ (43627559585957/100000000000000 : ℝ)^3891 := by
    have hnat : (5185776347 : ℕ)^4915*100000000000000^3891 ≤ 43627559585957^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185776347 10000000000 43627559585957 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722942021/5000000000 : ℝ)^4915 ≤ (46409739722607/100000000000000 : ℝ)^3891 := by
    have hnat : (2722942021 : ℕ)^4915*100000000000000^3891 ≤ 46409739722607^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722942021 5000000000 46409739722607 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201357137/1250000000 : ℝ), (5185776347/10000000000 : ℝ), (2722942021/5000000000 : ℝ)] ![(9962700670261/100000000000000 : ℝ), (43627559585957/100000000000000 : ℝ), (46409739722607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201357137/1250000000 : ℝ)|^4915 ≤ (9962700670261/100000000000000 : ℝ)^3891
        have hw : |(-201357137/1250000000 : ℝ)|=(201357137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185776347/10000000000 : ℝ)|^4915 ≤ (43627559585957/100000000000000 : ℝ)^3891
        have hw : |(5185776347/10000000000 : ℝ)|=(5185776347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722942021/5000000000 : ℝ)|^4915 ≤ (46409739722607/100000000000000 : ℝ)^3891
        have hw : |(2722942021/5000000000 : ℝ)|=(2722942021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_5 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277359717/10000000000 : ℝ)*x 0 + (-371165803/2500000000 : ℝ)*x 1 + (217835367/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277359717/10000000000 : ℝ)^4915 ≤ (8920613046473/20000000000000 : ℝ)^3891 := by
    have hnat : (5277359717 : ℕ)^4915*20000000000000^3891 ≤ 8920613046473^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277359717 10000000000 8920613046473 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371165803/2500000000 : ℝ)^4915 ≤ (898719359533/10000000000000 : ℝ)^3891 := by
    have hnat : (371165803 : ℕ)^4915*10000000000000^3891 ≤ 898719359533^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371165803 2500000000 898719359533 10000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217835367/400000000 : ℝ)^4915 ≤ (9281948230863/20000000000000 : ℝ)^3891 := by
    have hnat : (217835367 : ℕ)^4915*20000000000000^3891 ≤ 9281948230863^3891*400000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217835367 400000000 9281948230863 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277359717/10000000000 : ℝ), (-371165803/2500000000 : ℝ), (217835367/400000000 : ℝ)] ![(8920613046473/20000000000000 : ℝ), (898719359533/10000000000000 : ℝ), (9281948230863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277359717/10000000000 : ℝ)|^4915 ≤ (8920613046473/20000000000000 : ℝ)^3891
        have hw : |(5277359717/10000000000 : ℝ)|=(5277359717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-371165803/2500000000 : ℝ)|^4915 ≤ (898719359533/10000000000000 : ℝ)^3891
        have hw : |(-371165803/2500000000 : ℝ)|=(371165803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217835367/400000000 : ℝ)|^4915 ≤ (9281948230863/20000000000000 : ℝ)^3891
        have hw : |(217835367/400000000 : ℝ)|=(217835367/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_6 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211094389/400000000 : ℝ)*x 0 + (680735511/1250000000 : ℝ)*x 1 + (-371165831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211094389/400000000 : ℝ)^4915 ≤ (44603065317773/100000000000000 : ℝ)^3891 := by
    have hnat : (211094389 : ℕ)^4915*100000000000000^3891 ≤ 44603065317773^3891*400000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211094389 400000000 44603065317773 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680735511/1250000000 : ℝ)^4915 ≤ (5801217527223/12500000000000 : ℝ)^3891 := by
    have hnat : (680735511 : ℕ)^4915*12500000000000^3891 ≤ 5801217527223^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680735511 1250000000 5801217527223 12500000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371165831/2500000000 : ℝ)^4915 ≤ (898719445173/10000000000000 : ℝ)^3891 := by
    have hnat : (371165831 : ℕ)^4915*10000000000000^3891 ≤ 898719445173^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371165831 2500000000 898719445173 10000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211094389/400000000 : ℝ), (680735511/1250000000 : ℝ), (-371165831/2500000000 : ℝ)] ![(44603065317773/100000000000000 : ℝ), (5801217527223/12500000000000 : ℝ), (898719445173/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211094389/400000000 : ℝ)|^4915 ≤ (44603065317773/100000000000000 : ℝ)^3891
        have hw : |(211094389/400000000 : ℝ)|=(211094389/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680735511/1250000000 : ℝ)|^4915 ≤ (5801217527223/12500000000000 : ℝ)^3891
        have hw : |(680735511/1250000000 : ℝ)|=(680735511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-371165831/2500000000 : ℝ)|^4915 ≤ (898719445173/10000000000000 : ℝ)^3891
        have hw : |(-371165831/2500000000 : ℝ)|=(371165831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s3_7 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522706343/1250000000 : ℝ)*x 0 + (1131920737/2500000000 : ℝ)*x 1 + (963891457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522706343/1250000000 : ℝ)^4915 ≤ (33242777927241/100000000000000 : ℝ)^3891 := by
    have hnat : (522706343 : ℕ)^4915*100000000000000^3891 ≤ 33242777927241^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522706343 1250000000 33242777927241 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131920737/2500000000 : ℝ)^4915 ≤ (367546598213/1000000000000 : ℝ)^3891 := by
    have hnat : (1131920737 : ℕ)^4915*1000000000000^3891 ≤ 367546598213^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131920737 2500000000 367546598213 1000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963891457/2500000000 : ℝ)^4915 ≤ (15001281120477/50000000000000 : ℝ)^3891 := by
    have hnat : (963891457 : ℕ)^4915*50000000000000^3891 ≤ 15001281120477^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963891457 2500000000 15001281120477 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522706343/1250000000 : ℝ), (1131920737/2500000000 : ℝ), (963891457/2500000000 : ℝ)] ![(33242777927241/100000000000000 : ℝ), (367546598213/1000000000000 : ℝ), (15001281120477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522706343/1250000000 : ℝ)|^4915 ≤ (33242777927241/100000000000000 : ℝ)^3891
        have hw : |(522706343/1250000000 : ℝ)|=(522706343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131920737/2500000000 : ℝ)|^4915 ≤ (367546598213/1000000000000 : ℝ)^3891
        have hw : |(1131920737/2500000000 : ℝ)|=(1131920737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963891457/2500000000 : ℝ)|^4915 ≤ (15001281120477/50000000000000 : ℝ)^3891
        have hw : |(963891457/2500000000 : ℝ)|=(963891457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1649_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10661/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (651/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16349/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16349/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16349/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16349/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16349/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16349/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5297/50000 : ℝ) ^ (4911/1024 : ℝ) ≤ (527505066727821/25000000000000000000 : ℝ) := by
    have hpowers : (5297/50000 : ℝ)^4911 ≤ (527505066727821/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5297 : ℕ)^4911*25000000000000000000^1024 ≤ 527505066727821^1024*50000^4911 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5297 50000 527505066727821 25000000000000000000 4911 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5297/50000 : ℝ)) (X := (527505066727821/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16349/100000 : ℝ) ^ (4911/1024 : ℝ) ≤ (132060724570273/781250000000000000 : ℝ) := by
    have hpowers : (16349/100000 : ℝ)^4911 ≤ (132060724570273/781250000000000000 : ℝ)^1024 := by
      have hnat : (16349 : ℕ)^4911*781250000000000000^1024 ≤ 132060724570273^1024*100000^4911 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16349 100000 132060724570273 781250000000000000 4911 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16349/100000 : ℝ)) (X := (132060724570273/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500527505066727821/12500000000000000000 : ℝ) ≤ (5000043995615353/5000000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (12500527505066727821/12500000000000000000 : ℝ)^1024 ≤ (5000043995615353/5000000000000000 : ℝ)^4911 := by
      have hnat : (12500527505066727821 : ℕ)^1024*5000000000000000^4911 ≤ 5000043995615353^4911*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500527505066727821 12500000000000000000 5000043995615353 5000000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000043995615353/5000000000000000 : ℝ)) (X := (12500527505066727821/12500000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004753448252976557/25000000000000000000 : ℝ) ≤ (10000396429630661/10000000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (25004753448252976557/25000000000000000000 : ℝ)^1024 ≤ (10000396429630661/10000000000000000 : ℝ)^4911 := by
      have hnat : (25004753448252976557 : ℕ)^1024*10000000000000000^4911 ≤ 10000396429630661^4911*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004753448252976557 25000000000000000000 10000396429630661 10000000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000396429630661/10000000000000000 : ℝ)) (X := (25004753448252976557/25000000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (390757060724570273/390625000000000000 : ℝ) ≤ (1250088108503827/1250000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (390757060724570273/390625000000000000 : ℝ)^1024 ≤ (1250088108503827/1250000000000000 : ℝ)^4911 := by
      have hnat : (390757060724570273 : ℕ)^1024*1250000000000000^4911 ≤ 1250088108503827^4911*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390757060724570273 390625000000000000 1250088108503827 1250000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250088108503827/1250000000000000 : ℝ)) (X := (390757060724570273/390625000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(527505066727821/25000000000000000000 : ℝ) ≤ ((5754397119671446649/5755000000000000000 : ℝ)+2*(61687679991/115100000000000 : ℝ)*(5297/50000 : ℝ))^(4911/1024 : ℝ) := by
    rw [show (5754397119671446649/5755000000000000000 : ℝ)+2*(61687679991/115100000000000 : ℝ)*(5297/50000 : ℝ)=(5000043995615353/5000000000000000 : ℝ) by norm_num, show 1+2*(527505066727821/25000000000000000000 : ℝ)=(12500527505066727821/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(132060724570273/781250000000000000 : ℝ)+(527505066727821/25000000000000000000 : ℝ) ≤ ((5754397119671446649/5755000000000000000 : ℝ)+(61687679991/115100000000000 : ℝ)*((16349/100000 : ℝ)+(5297/50000 : ℝ)))^(4911/1024 : ℝ) := by
    rw [show (5754397119671446649/5755000000000000000 : ℝ)+(61687679991/115100000000000 : ℝ)*((16349/100000 : ℝ)+(5297/50000 : ℝ))=(10000396429630661/10000000000000000 : ℝ) by norm_num, show 1+(132060724570273/781250000000000000 : ℝ)+(527505066727821/25000000000000000000 : ℝ)=(25004753448252976557/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(132060724570273/781250000000000000 : ℝ) ≤ ((5754397119671446649/5755000000000000000 : ℝ)+2*(61687679991/115100000000000 : ℝ)*(16349/100000 : ℝ))^(4911/1024 : ℝ) := by
    rw [show (5754397119671446649/5755000000000000000 : ℝ)+2*(61687679991/115100000000000 : ℝ)*(16349/100000 : ℝ)=(1250088108503827/1250000000000000 : ℝ) by norm_num, show 1+2*(132060724570273/781250000000000000 : ℝ)=(390757060724570273/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5754397119671446649/5755000000000000000 : ℝ)*(X 1 0+X 2 0)+(61687679991/115100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (5754397119671446649/5755000000000000000 : ℝ)) (alpha := (61687679991/115100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5754397119671446649/5755000000000000000 : ℝ)*(X 0 1+X 2 1)+(61687679991/115100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (5754397119671446649/5755000000000000000 : ℝ)) (alpha := (61687679991/115100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5754397119671446649/5755000000000000000 : ℝ)*(X 0 2+X 1 2)+(61687679991/115100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (5754397119671446649/5755000000000000000 : ℝ)) (alpha := (61687679991/115100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1610792779/10000000000 : ℝ)*X 0 0+(1089580861/2000000000 : ℝ)*X 0 1+(323986061/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347914321/10000000000 : ℝ)*X 1 0+(-1746770273/10000000000 : ℝ)*X 1 1+(5183777001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534791429/1000000000 : ℝ)*X 2 0+(5183776997/10000000000 : ℝ)*X 2 1+(-873385159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((418148381/1000000000 : ℝ)*X 0 0+(481293223/1250000000 : ℝ)*X 0 1+(90656973/200000000 : ℝ)*X 0 2+(418148381/1000000000 : ℝ)*X 1 0+(481293223/1250000000 : ℝ)*X 1 1+(90656973/200000000 : ℝ)*X 1 2+(418148381/1000000000 : ℝ)*X 2 0+(481293223/1250000000 : ℝ)*X 2 1+(90656973/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-201357137/1250000000 : ℝ)*X 0 0+(5185776347/10000000000 : ℝ)*X 0 1+(2722942021/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277359717/10000000000 : ℝ)*X 1 0+(-371165803/2500000000 : ℝ)*X 1 1+(217835367/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211094389/400000000 : ℝ)*X 2 0+(680735511/1250000000 : ℝ)*X 2 1+(-371165831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522706343/1250000000 : ℝ)*X 0 0+(1131920737/2500000000 : ℝ)*X 0 1+(963891457/2500000000 : ℝ)*X 0 2+(522706343/1250000000 : ℝ)*X 1 0+(1131920737/2500000000 : ℝ)*X 1 1+(963891457/2500000000 : ℝ)*X 1 2+(522706343/1250000000 : ℝ)*X 2 0+(1131920737/2500000000 : ℝ)*X 2 1+(963891457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (149167867623469663978874859/35968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797854231/100000000000000 : ℝ)*(base19) + (354441979/50000000000000 : ℝ)*(base23) + (17921857/50000000000000 : ℝ)*(lower2) + (28484649/20000000000000 : ℝ)*(upper3) + (54981849/100000000000000 : ℝ)*(upper5) + (328204807979199/12500000000000 : ℝ)*(major0) + (328204807979199/12500000000000 : ℝ)*(major1) + (328204807979199/12500000000000 : ℝ)*(major2) + (3786063821750389/100000000000000 : ℝ)*(sp0) + (757214522364529/20000000000000 : ℝ)*(sp1) + (1893036350396459/50000000000000 : ℝ)*(sp2) + (732599455085499/50000000000000 : ℝ)*(sp3) + (9587926487/100000000000000 : ℝ)*(sp4) + (1117395227/25000000000000 : ℝ)*(sp7) + (732601689875953/50000000000000 : ℝ)*(f.failure) + (946518352419219/25000000000000 : ℝ)*(f.sum) + (20070534975177/5755000000000000000000000000 : ℝ)*base65 + (942633905406170849/71937500000000000000000000000000 : ℝ)*base68 + (864486169943170849/71937500000000000000000000000000 : ℝ)*base70 + (429516675792233349/71937500000000000000000000000000 : ℝ)*base72 + (34999646931233/5755000000000000000000000000 : ℝ)*base74 + (1001334568666733349/71937500000000000000000000000000 : ℝ)*base76 + (673773203943795849/71937500000000000000000000000000 : ℝ)*base78 + (371520626244420849/71937500000000000000000000000000 : ℝ)*base80 + (151245557427/89921875000000000000000000 : ℝ)*base82 + (18335223/5000000000000000000000 : ℝ)*base89 + (18335223/5000000000000000000000 : ℝ)*base91 + (18335223/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (750486628538967362522162997/71937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1216810043/100000000000000 : ℝ)*(base19) + (1626530799/100000000000000 : ℝ)*(base23) + (248486723/100000000000000 : ℝ)*(upper3) + (17980071/10000000000000 : ℝ)*(lower4) + (133836041/100000000000000 : ℝ)*(upper5) + (666549032014349/25000000000000 : ℝ)*(major0) + (666549032014349/25000000000000 : ℝ)*(major1) + (666549032014349/25000000000000 : ℝ)*(major2) + (6806285613/50000000000000 : ℝ)*(sp1) + (4584784271/25000000000000 : ℝ)*(sp2) + (3844555851832559/100000000000000 : ℝ)*(sp4) + (384454102245129/10000000000000 : ℝ)*(sp5) + (961133971541169/25000000000000 : ℝ)*(sp6) + (29756721130657/2000000000000 : ℝ)*(sp7) + (29756721130657/2000000000000 : ℝ)*(f.failure) + (3844555851832559/100000000000000 : ℝ)*(f.sum) + (5661065869311/1438750000000000000000000000 : ℝ)*base66 + (914396348558541501/143875000000000000000000000000000 : ℝ)*base67 + (296331001026666501/143875000000000000000000000000000 : ℝ)*base69 + (1571868551135583499/143875000000000000000000000000000 : ℝ)*base72 + (17579530384413/2877500000000000000000000000 : ℝ)*base73 + (840410787501916501/143875000000000000000000000000000 : ℝ)*base75 + (149740852166416501/143875000000000000000000000000000 : ℝ)*base77 + (262249408030583499/143875000000000000000000000000000 : ℝ)*base80 + (1459458818721/1438750000000000000000000000 : ℝ)*base82 + (38713/200000000000000000000 : ℝ)*base90 + (38713/200000000000000000000 : ℝ)*base92 + (38713/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1649_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10661/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (651/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1649_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1649_s4_0 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12886709/80000000 : ℝ)*x 0 + (680958669/1250000000 : ℝ)*x 1 + (5183981313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12886709/80000000 : ℝ)^4915 ≤ (498127818417/5000000000000 : ℝ)^3891 := by
    have hnat : (12886709 : ℕ)^4915*5000000000000^3891 ≤ 498127818417^3891*80000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12886709 80000000 498127818417 5000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680958669/1250000000 : ℝ)^4915 ≤ (46428958926953/100000000000000 : ℝ)^3891 := by
    have hnat : (680958669 : ℕ)^4915*100000000000000^3891 ≤ 46428958926953^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680958669 1250000000 46428958926953 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183981313/10000000000 : ℝ)^4915 ≤ (21804242341769/50000000000000 : ℝ)^3891 := by
    have hnat : (5183981313 : ℕ)^4915*50000000000000^3891 ≤ 21804242341769^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183981313 10000000000 21804242341769 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12886709/80000000 : ℝ), (680958669/1250000000 : ℝ), (5183981313/10000000000 : ℝ)] ![(498127818417/5000000000000 : ℝ), (46428958926953/100000000000000 : ℝ), (21804242341769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12886709/80000000 : ℝ)|^4915 ≤ (498127818417/5000000000000 : ℝ)^3891
        have hw : |(-12886709/80000000 : ℝ)|=(12886709/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680958669/1250000000 : ℝ)|^4915 ≤ (46428958926953/100000000000000 : ℝ)^3891
        have hw : |(680958669/1250000000 : ℝ)|=(680958669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183981313/10000000000 : ℝ)|^4915 ≤ (21804242341769/50000000000000 : ℝ)^3891
        have hw : |(5183981313/10000000000 : ℝ)|=(5183981313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_1 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347850737/10000000000 : ℝ)*x 0 + (-54580737/312500000 : ℝ)*x 1 + (129599533/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347850737/10000000000 : ℝ)^4915 ≤ (22678474389207/50000000000000 : ℝ)^3891 := by
    have hnat : (5347850737 : ℕ)^4915*50000000000000^3891 ≤ 22678474389207^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347850737 10000000000 22678474389207 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54580737/312500000 : ℝ)^4915 ≤ (137932080667/1250000000000 : ℝ)^3891 := by
    have hnat : (54580737 : ℕ)^4915*1250000000000^3891 ≤ 137932080667^3891*312500000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54580737 312500000 137932080667 1250000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129599533/250000000 : ℝ)^4915 ≤ (272553029737/625000000000 : ℝ)^3891 := by
    have hnat : (129599533 : ℕ)^4915*625000000000^3891 ≤ 272553029737^3891*250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129599533 250000000 272553029737 625000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347850737/10000000000 : ℝ), (-54580737/312500000 : ℝ), (129599533/250000000 : ℝ)] ![(22678474389207/50000000000000 : ℝ), (137932080667/1250000000000 : ℝ), (272553029737/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347850737/10000000000 : ℝ)|^4915 ≤ (22678474389207/50000000000000 : ℝ)^3891
        have hw : |(5347850737/10000000000 : ℝ)|=(5347850737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54580737/312500000 : ℝ)|^4915 ≤ (137932080667/1250000000000 : ℝ)^3891
        have hw : |(-54580737/312500000 : ℝ)|=(54580737/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129599533/250000000 : ℝ)|^4915 ≤ (272553029737/625000000000 : ℝ)^3891
        have hw : |(129599533/250000000 : ℝ)|=(129599533/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_2 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347850739/10000000000 : ℝ)*x 0 + (5183981317/10000000000 : ℝ)*x 1 + (-873291793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347850739/10000000000 : ℝ)^4915 ≤ (283480929999/625000000000 : ℝ)^3891 := by
    have hnat : (5347850739 : ℕ)^4915*625000000000^3891 ≤ 283480929999^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347850739 10000000000 283480929999 625000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183981317/10000000000 : ℝ)^4915 ≤ (21804242363021/50000000000000 : ℝ)^3891 := by
    have hnat : (5183981317 : ℕ)^4915*50000000000000^3891 ≤ 21804242363021^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183981317 10000000000 21804242363021 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873291793/5000000000 : ℝ)^4915 ≤ (11034566469321/100000000000000 : ℝ)^3891 := by
    have hnat : (873291793 : ℕ)^4915*100000000000000^3891 ≤ 11034566469321^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873291793 5000000000 11034566469321 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347850739/10000000000 : ℝ), (5183981317/10000000000 : ℝ), (-873291793/5000000000 : ℝ)] ![(283480929999/625000000000 : ℝ), (21804242363021/50000000000000 : ℝ), (11034566469321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347850739/10000000000 : ℝ)|^4915 ≤ (283480929999/625000000000 : ℝ)^3891
        have hw : |(5347850739/10000000000 : ℝ)|=(5347850739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183981317/10000000000 : ℝ)|^4915 ≤ (21804242363021/50000000000000 : ℝ)^3891
        have hw : |(5183981317/10000000000 : ℝ)|=(5183981317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-873291793/5000000000 : ℝ)|^4915 ≤ (11034566469321/100000000000000 : ℝ)^3891
        have hw : |(-873291793/5000000000 : ℝ)|=(873291793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_3 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181514191/10000000000 : ℝ)*x 0 + (481363793/1250000000 : ℝ)*x 1 + (226613903/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181514191/10000000000 : ℝ)^4915 ≤ (33241406694349/100000000000000 : ℝ)^3891 := by
    have hnat : (4181514191 : ℕ)^4915*100000000000000^3891 ≤ 33241406694349^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181514191 10000000000 33241406694349 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481363793/1250000000 : ℝ)^4915 ≤ (29956808319379/100000000000000 : ℝ)^3891 := by
    have hnat : (481363793 : ℕ)^4915*100000000000000^3891 ≤ 29956808319379^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481363793 1250000000 29956808319379 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226613903/500000000 : ℝ)^4915 ≤ (18400892487091/50000000000000 : ℝ)^3891 := by
    have hnat : (226613903 : ℕ)^4915*50000000000000^3891 ≤ 18400892487091^3891*500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226613903 500000000 18400892487091 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181514191/10000000000 : ℝ), (481363793/1250000000 : ℝ), (226613903/500000000 : ℝ)] ![(33241406694349/100000000000000 : ℝ), (29956808319379/100000000000000 : ℝ), (18400892487091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181514191/10000000000 : ℝ)|^4915 ≤ (33241406694349/100000000000000 : ℝ)^3891
        have hw : |(4181514191/10000000000 : ℝ)|=(4181514191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481363793/1250000000 : ℝ)|^4915 ≤ (29956808319379/100000000000000 : ℝ)^3891
        have hw : |(481363793/1250000000 : ℝ)|=(481363793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226613903/500000000 : ℝ)|^4915 ≤ (18400892487091/50000000000000 : ℝ)^3891
        have hw : |(226613903/500000000 : ℝ)|=(226613903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_4 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-805451433/5000000000 : ℝ)*x 0 + (1296493453/2500000000 : ℝ)*x 1 + (2722827943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (805451433/5000000000 : ℝ)^4915 ≤ (9963058243407/100000000000000 : ℝ)^3891 := by
    have hnat : (805451433 : ℕ)^4915*100000000000000^3891 ≤ 9963058243407^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805451433 5000000000 9963058243407 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296493453/2500000000 : ℝ)^4915 ≤ (2181482902549/5000000000000 : ℝ)^3891 := by
    have hnat : (1296493453 : ℕ)^4915*5000000000000^3891 ≤ 2181482902549^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296493453 2500000000 2181482902549 5000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722827943/5000000000 : ℝ)^4915 ≤ (46407283699013/100000000000000 : ℝ)^3891 := by
    have hnat : (2722827943 : ℕ)^4915*100000000000000^3891 ≤ 46407283699013^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722827943 5000000000 46407283699013 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-805451433/5000000000 : ℝ), (1296493453/2500000000 : ℝ), (2722827943/5000000000 : ℝ)] ![(9963058243407/100000000000000 : ℝ), (2181482902549/5000000000000 : ℝ), (46407283699013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-805451433/5000000000 : ℝ)|^4915 ≤ (9963058243407/100000000000000 : ℝ)^3891
        have hw : |(-805451433/5000000000 : ℝ)|=(805451433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296493453/2500000000 : ℝ)|^4915 ≤ (2181482902549/5000000000000 : ℝ)^3891
        have hw : |(1296493453/2500000000 : ℝ)|=(1296493453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722827943/5000000000 : ℝ)|^4915 ≤ (46407283699013/100000000000000 : ℝ)^3891
        have hw : |(2722827943/5000000000 : ℝ)|=(2722827943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_5 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277413847/10000000000 : ℝ)*x 0 + (-185613627/1250000000 : ℝ)*x 1 + (2722827943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277413847/10000000000 : ℝ)^4915 ≤ (11150910781833/25000000000000 : ℝ)^3891 := by
    have hnat : (5277413847 : ℕ)^4915*25000000000000^3891 ≤ 11150910781833^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277413847 10000000000 11150910781833 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185613627/1250000000 : ℝ)^4915 ≤ (112363414477/1250000000000 : ℝ)^3891 := by
    have hnat : (185613627 : ℕ)^4915*1250000000000^3891 ≤ 112363414477^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185613627 1250000000 112363414477 1250000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722827943/5000000000 : ℝ)^4915 ≤ (46407283699013/100000000000000 : ℝ)^3891 := by
    have hnat : (2722827943 : ℕ)^4915*100000000000000^3891 ≤ 46407283699013^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722827943 5000000000 46407283699013 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277413847/10000000000 : ℝ), (-185613627/1250000000 : ℝ), (2722827943/5000000000 : ℝ)] ![(11150910781833/25000000000000 : ℝ), (112363414477/1250000000000 : ℝ), (46407283699013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277413847/10000000000 : ℝ)|^4915 ≤ (11150910781833/25000000000000 : ℝ)^3891
        have hw : |(5277413847/10000000000 : ℝ)|=(5277413847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185613627/1250000000 : ℝ)|^4915 ≤ (112363414477/1250000000000 : ℝ)^3891
        have hw : |(-185613627/1250000000 : ℝ)|=(185613627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722827943/5000000000 : ℝ)|^4915 ≤ (46407283699013/100000000000000 : ℝ)^3891
        have hw : |(2722827943/5000000000 : ℝ)|=(2722827943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_6 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277413847/10000000000 : ℝ)*x 0 + (2722827943/5000000000 : ℝ)*x 1 + (-185613627/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277413847/10000000000 : ℝ)^4915 ≤ (11150910781833/25000000000000 : ℝ)^3891 := by
    have hnat : (5277413847 : ℕ)^4915*25000000000000^3891 ≤ 11150910781833^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277413847 10000000000 11150910781833 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722827943/5000000000 : ℝ)^4915 ≤ (46407283699013/100000000000000 : ℝ)^3891 := by
    have hnat : (2722827943 : ℕ)^4915*100000000000000^3891 ≤ 46407283699013^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722827943 5000000000 46407283699013 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185613627/1250000000 : ℝ)^4915 ≤ (112363414477/1250000000000 : ℝ)^3891 := by
    have hnat : (185613627 : ℕ)^4915*1250000000000^3891 ≤ 112363414477^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185613627 1250000000 112363414477 1250000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277413847/10000000000 : ℝ), (2722827943/5000000000 : ℝ), (-185613627/1250000000 : ℝ)] ![(11150910781833/25000000000000 : ℝ), (46407283699013/100000000000000 : ℝ), (112363414477/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277413847/10000000000 : ℝ)|^4915 ≤ (11150910781833/25000000000000 : ℝ)^3891
        have hw : |(5277413847/10000000000 : ℝ)|=(5277413847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722827943/5000000000 : ℝ)|^4915 ≤ (46407283699013/100000000000000 : ℝ)^3891
        have hw : |(2722827943/5000000000 : ℝ)|=(2722827943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-185613627/1250000000 : ℝ)|^4915 ≤ (112363414477/1250000000000 : ℝ)^3891
        have hw : |(-185613627/1250000000 : ℝ)|=(185613627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_s4_7 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181680189/10000000000 : ℝ)*x 0 + (452712947/1000000000 : ℝ)*x 1 + (3856113113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181680189/10000000000 : ℝ)^4915 ≤ (33243073608503/100000000000000 : ℝ)^3891 := by
    have hnat : (4181680189 : ℕ)^4915*100000000000000^3891 ≤ 33243073608503^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181680189 10000000000 33243073608503 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452712947/1000000000 : ℝ)^4915 ≤ (367489844789/1000000000000 : ℝ)^3891 := by
    have hnat : (452712947 : ℕ)^4915*1000000000000^3891 ≤ 367489844789^3891*1000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452712947 1000000000 367489844789 1000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3856113113/10000000000 : ℝ)^4915 ≤ (15003970946403/50000000000000 : ℝ)^3891 := by
    have hnat : (3856113113 : ℕ)^4915*50000000000000^3891 ≤ 15003970946403^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856113113 10000000000 15003970946403 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181680189/10000000000 : ℝ), (452712947/1000000000 : ℝ), (3856113113/10000000000 : ℝ)] ![(33243073608503/100000000000000 : ℝ), (367489844789/1000000000000 : ℝ), (15003970946403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181680189/10000000000 : ℝ)|^4915 ≤ (33243073608503/100000000000000 : ℝ)^3891
        have hw : |(4181680189/10000000000 : ℝ)|=(4181680189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452712947/1000000000 : ℝ)|^4915 ≤ (367489844789/1000000000000 : ℝ)^3891
        have hw : |(452712947/1000000000 : ℝ)|=(452712947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3856113113/10000000000 : ℝ)|^4915 ≤ (15003970946403/50000000000000 : ℝ)^3891
        have hw : |(3856113113/10000000000 : ℝ)|=(3856113113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1649_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2133/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1627/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (651/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (651/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10661/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (651/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (651/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10661/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (651/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (651/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10661/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10661/100000 : ℝ) ^ (4911/1024 : ℝ) ≤ (434958348726311/20000000000000000000 : ℝ) := by
    have hpowers : (10661/100000 : ℝ)^4911 ≤ (434958348726311/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10661 : ℕ)^4911*20000000000000000000^1024 ≤ 434958348726311^1024*100000^4911 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10661 100000 434958348726311 20000000000000000000 4911 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10661/100000 : ℝ)) (X := (434958348726311/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (651/4000 : ℝ) ^ (4911/1024 : ℝ) ≤ (4134993120435417/25000000000000000000 : ℝ) := by
    have hpowers : (651/4000 : ℝ)^4911 ≤ (4134993120435417/25000000000000000000 : ℝ)^1024 := by
      have hnat : (651 : ℕ)^4911*25000000000000000000^1024 ≤ 4134993120435417^1024*4000^4911 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651 4000 4134993120435417 25000000000000000000 4911 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (651/4000 : ℝ)) (X := (4134993120435417/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000434958348726311/10000000000000000000 : ℝ) ≤ (62500566826617/62500000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (10000434958348726311/10000000000000000000 : ℝ)^1024 ≤ (62500566826617/62500000000000 : ℝ)^4911 := by
      have hnat : (10000434958348726311 : ℕ)^1024*62500000000000^4911 ≤ 62500566826617^4911*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000434958348726311 10000000000000000000 62500566826617 62500000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500566826617/62500000000000 : ℝ)) (X := (10000434958348726311/10000000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018714764225373223/100000000000000000000 : ℝ) ≤ (10000390195467231/10000000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (100018714764225373223/100000000000000000000 : ℝ)^1024 ≤ (10000390195467231/10000000000000000 : ℝ)^4911 := by
      have hnat : (100018714764225373223 : ℕ)^1024*10000000000000000^4911 ≤ 10000390195467231^4911*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018714764225373223 100000000000000000000 10000390195467231 10000000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000390195467231/10000000000000000 : ℝ)) (X := (100018714764225373223/100000000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504134993120435417/12500000000000000000 : ℝ) ≤ (5000344849337871/5000000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (12504134993120435417/12500000000000000000 : ℝ)^1024 ≤ (5000344849337871/5000000000000000 : ℝ)^4911 := by
      have hnat : (12504134993120435417 : ℕ)^1024*5000000000000000^4911 ≤ 5000344849337871^4911*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504134993120435417 12500000000000000000 5000344849337871 5000000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344849337871/5000000000000000 : ℝ)) (X := (12504134993120435417/12500000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(434958348726311/20000000000000000000 : ℝ) ≤ ((4009580224209184467/4010000000000000000 : ℝ)+2*(299503208511/561400000000000 : ℝ)*(10661/100000 : ℝ))^(4911/1024 : ℝ) := by
    rw [show (4009580224209184467/4010000000000000000 : ℝ)+2*(299503208511/561400000000000 : ℝ)*(10661/100000 : ℝ)=(62500566826617/62500000000000 : ℝ) by norm_num, show 1+2*(434958348726311/20000000000000000000 : ℝ)=(10000434958348726311/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4134993120435417/25000000000000000000 : ℝ)+(434958348726311/20000000000000000000 : ℝ) ≤ ((4009580224209184467/4010000000000000000 : ℝ)+(299503208511/561400000000000 : ℝ)*((651/4000 : ℝ)+(10661/100000 : ℝ)))^(4911/1024 : ℝ) := by
    rw [show (4009580224209184467/4010000000000000000 : ℝ)+(299503208511/561400000000000 : ℝ)*((651/4000 : ℝ)+(10661/100000 : ℝ))=(10000390195467231/10000000000000000 : ℝ) by norm_num, show 1+(4134993120435417/25000000000000000000 : ℝ)+(434958348726311/20000000000000000000 : ℝ)=(100018714764225373223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4134993120435417/25000000000000000000 : ℝ) ≤ ((4009580224209184467/4010000000000000000 : ℝ)+2*(299503208511/561400000000000 : ℝ)*(651/4000 : ℝ))^(4911/1024 : ℝ) := by
    rw [show (4009580224209184467/4010000000000000000 : ℝ)+2*(299503208511/561400000000000 : ℝ)*(651/4000 : ℝ)=(5000344849337871/5000000000000000 : ℝ) by norm_num, show 1+2*(4134993120435417/25000000000000000000 : ℝ)=(12504134993120435417/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4009580224209184467/4010000000000000000 : ℝ)*(X 1 0+X 2 0)+(299503208511/561400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (10661/100000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (4009580224209184467/4010000000000000000 : ℝ)) (alpha := (299503208511/561400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4009580224209184467/4010000000000000000 : ℝ)*(X 0 1+X 2 1)+(299503208511/561400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (10661/100000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (4009580224209184467/4010000000000000000 : ℝ)) (alpha := (299503208511/561400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4009580224209184467/4010000000000000000 : ℝ)*(X 0 2+X 1 2)+(299503208511/561400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (10661/100000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (4009580224209184467/4010000000000000000 : ℝ)) (alpha := (299503208511/561400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-12886709/80000000 : ℝ)*X 0 0+(680958669/1250000000 : ℝ)*X 0 1+(5183981313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347850737/10000000000 : ℝ)*X 1 0+(-54580737/312500000 : ℝ)*X 1 1+(129599533/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347850739/10000000000 : ℝ)*X 2 0+(5183981317/10000000000 : ℝ)*X 2 1+(-873291793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4181514191/10000000000 : ℝ)*X 0 0+(481363793/1250000000 : ℝ)*X 0 1+(226613903/500000000 : ℝ)*X 0 2+(4181514191/10000000000 : ℝ)*X 1 0+(481363793/1250000000 : ℝ)*X 1 1+(226613903/500000000 : ℝ)*X 1 2+(4181514191/10000000000 : ℝ)*X 2 0+(481363793/1250000000 : ℝ)*X 2 1+(226613903/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-805451433/5000000000 : ℝ)*X 0 0+(1296493453/2500000000 : ℝ)*X 0 1+(2722827943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277413847/10000000000 : ℝ)*X 1 0+(-185613627/1250000000 : ℝ)*X 1 1+(2722827943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277413847/10000000000 : ℝ)*X 2 0+(2722827943/5000000000 : ℝ)*X 2 1+(-185613627/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4181680189/10000000000 : ℝ)*X 0 0+(452712947/1000000000 : ℝ)*X 0 1+(3856113113/10000000000 : ℝ)*X 0 2+(4181680189/10000000000 : ℝ)*X 1 0+(452712947/1000000000 : ℝ)*X 1 1+(3856113113/10000000000 : ℝ)*X 1 2+(4181680189/10000000000 : ℝ)*X 2 0+(452712947/1000000000 : ℝ)*X 2 1+(3856113113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17796610579230848061579/2005000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1404265523/100000000000000 : ℝ)*(base19) + (1316556049/100000000000000 : ℝ)*(base23) + (47664197/100000000000000 : ℝ)*(lower2) + (217485101/100000000000000 : ℝ)*(upper3) + (76270197/50000000000000 : ℝ)*(upper5) + (1315011616837527/50000000000000 : ℝ)*(major0) + (1315011616837527/50000000000000 : ℝ)*(major1) + (1315011616837527/50000000000000 : ℝ)*(major2) + (1896189146421997/50000000000000 : ℝ)*(sp0) + (1896197261853537/50000000000000 : ℝ)*(sp1) + (3792394611416549/100000000000000 : ℝ)*(sp2) + (733821430873167/50000000000000 : ℝ)*(sp3) + (17635128603/100000000000000 : ℝ)*(sp4) + (7381760669/100000000000000 : ℝ)*(sp7) + (1467650243507003/100000000000000 : ℝ)*(f.failure) + (1896197963986299/50000000000000 : ℝ)*(f.sum) + (627222398183/250625000000000000000000000 : ℝ)*base66 + (273943750259643109/200500000000000000000000000000000 : ℝ)*base67 + (47751515723856891/200500000000000000000000000000000 : ℝ)*base70 + (431132758198143109/200500000000000000000000000000000 : ℝ)*base71 + (4364657098079/2005000000000000000000000000 : ℝ)*base74 + (1040961608873856891/200500000000000000000000000000000 : ℝ)*base76 + (482567790511643109/200500000000000000000000000000000 : ℝ)*base77 + (22675650794856891/200500000000000000000000000000000 : ℝ)*base80 + (149387698721/31328125000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (56764227/10000000000000000000000 : ℝ)*base90 + (56764227/10000000000000000000000 : ℝ)*base92 + (56764227/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (912474236572497142837664991/100250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1342547779/100000000000000 : ℝ)*(base19) + (1451009807/100000000000000 : ℝ)*(base23) + (42048287/10000000000000 : ℝ)*(lower1) + (95479793/50000000000000 : ℝ)*(upper3) + (1953483/4000000000000 : ℝ)*(lower4) + (47101797/25000000000000 : ℝ)*(upper5) + (1335279036955591/50000000000000 : ℝ)*(major0) + (1335279036955591/50000000000000 : ℝ)*(major1) + (1335279036955591/50000000000000 : ℝ)*(major2) + (1192959639/100000000000000 : ℝ)*(sp2) + (481355707595519/12500000000000 : ℝ)*(sp4) + (3850844318216373/100000000000000 : ℝ)*(sp5) + (1925421508397353/50000000000000 : ℝ)*(sp6) + (372567545914653/25000000000000 : ℝ)*(sp7) + (372567545914653/25000000000000 : ℝ)*(f.failure) + (481355707595519/12500000000000 : ℝ)*(f.sum) + (5853911499963/2005000000000000000000000000 : ℝ)*base65 + (3982869231381154997/200500000000000000000000000000000 : ℝ)*base67 + (1242721118800845003/200500000000000000000000000000000 : ℝ)*base70 + (21729310388613654997/200500000000000000000000000000000 : ℝ)*base71 + (6908311765217/2005000000000000000000000000 : ℝ)*base74 + (4260731891403845003/200500000000000000000000000000000 : ℝ)*base76 + (488435515922345003/200500000000000000000000000000000 : ℝ)*base78 + (2014730707946345003/200500000000000000000000000000000 : ℝ)*base80 + (6812568471887/2005000000000000000000000000 : ℝ)*base82 + (11493077/2500000000000000000000 : ℝ)*base90 + (11493077/2500000000000000000000 : ℝ)*base92 + (11493077/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1649_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10661/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2133/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1627/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1649_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1649_box_0 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1352497669/10000000000 : ℝ)*x 0 + (338019481/625000000 : ℝ)*x 1 + (216332431/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352497669/10000000000 : ℝ)^4915 ≤ (7988706942187/100000000000000 : ℝ)^3891 := by
    have hnat : (1352497669 : ℕ)^4915*100000000000000^3891 ≤ 7988706942187^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352497669 10000000000 7988706942187 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338019481/625000000 : ℝ)^4915 ≤ (9201130293393/20000000000000 : ℝ)^3891 := by
    have hnat : (338019481 : ℕ)^4915*20000000000000^3891 ≤ 9201130293393^3891*625000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338019481 625000000 9201130293393 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216332431/400000000 : ℝ)^4915 ≤ (23002820785349/50000000000000 : ℝ)^3891 := by
    have hnat : (216332431 : ℕ)^4915*50000000000000^3891 ≤ 23002820785349^3891*400000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216332431 400000000 23002820785349 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1352497669/10000000000 : ℝ), (338019481/625000000 : ℝ), (216332431/400000000 : ℝ)] ![(7988706942187/100000000000000 : ℝ), (9201130293393/20000000000000 : ℝ), (23002820785349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1352497669/10000000000 : ℝ)|^4915 ≤ (7988706942187/100000000000000 : ℝ)^3891
        have hw : |(-1352497669/10000000000 : ℝ)|=(1352497669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338019481/625000000 : ℝ)|^4915 ≤ (9201130293393/20000000000000 : ℝ)^3891
        have hw : |(338019481/625000000 : ℝ)|=(338019481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216332431/400000000 : ℝ)|^4915 ≤ (23002820785349/50000000000000 : ℝ)^3891
        have hw : |(216332431/400000000 : ℝ)|=(216332431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_1 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625548021/5000000000 : ℝ)*x 0 + (-1573467831/10000000000 : ℝ)*x 1 + (67603887/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625548021/5000000000 : ℝ)^4915 ≤ (11080714240153/25000000000000 : ℝ)^3891 := by
    have hnat : (2625548021 : ℕ)^4915*25000000000000^3891 ≤ 11080714240153^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625548021 5000000000 11080714240153 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1573467831/10000000000 : ℝ)^4915 ≤ (4835749732237/50000000000000 : ℝ)^3891 := by
    have hnat : (1573467831 : ℕ)^4915*50000000000000^3891 ≤ 4835749732237^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573467831 10000000000 4835749732237 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67603887/125000000 : ℝ)^4915 ≤ (46005643558547/100000000000000 : ℝ)^3891 := by
    have hnat : (67603887 : ℕ)^4915*100000000000000^3891 ≤ 46005643558547^3891*125000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67603887 125000000 46005643558547 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625548021/5000000000 : ℝ), (-1573467831/10000000000 : ℝ), (67603887/125000000 : ℝ)] ![(11080714240153/25000000000000 : ℝ), (4835749732237/50000000000000 : ℝ), (46005643558547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625548021/5000000000 : ℝ)|^4915 ≤ (11080714240153/25000000000000 : ℝ)^3891
        have hw : |(2625548021/5000000000 : ℝ)|=(2625548021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1573467831/10000000000 : ℝ)|^4915 ≤ (4835749732237/50000000000000 : ℝ)^3891
        have hw : |(-1573467831/10000000000 : ℝ)|=(1573467831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67603887/125000000 : ℝ)|^4915 ≤ (46005643558547/100000000000000 : ℝ)^3891
        have hw : |(67603887/125000000 : ℝ)|=(67603887/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_2 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625547789/5000000000 : ℝ)*x 0 + (2704155659/5000000000 : ℝ)*x 1 + (-393366993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625547789/5000000000 : ℝ)^4915 ≤ (11080713003357/25000000000000 : ℝ)^3891 := by
    have hnat : (2625547789 : ℕ)^4915*25000000000000^3891 ≤ 11080713003357^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625547789 5000000000 11080713003357 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704155659/5000000000 : ℝ)^4915 ≤ (9201129481061/20000000000000 : ℝ)^3891 := by
    have hnat : (2704155659 : ℕ)^4915*20000000000000^3891 ≤ 9201129481061^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704155659 5000000000 9201129481061 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393366993/2500000000 : ℝ)^4915 ≤ (967150055923/10000000000000 : ℝ)^3891 := by
    have hnat : (393366993 : ℕ)^4915*10000000000000^3891 ≤ 967150055923^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393366993 2500000000 967150055923 10000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625547789/5000000000 : ℝ), (2704155659/5000000000 : ℝ), (-393366993/2500000000 : ℝ)] ![(11080713003357/25000000000000 : ℝ), (9201129481061/20000000000000 : ℝ), (967150055923/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625547789/5000000000 : ℝ)|^4915 ≤ (11080713003357/25000000000000 : ℝ)^3891
        have hw : |(2625547789/5000000000 : ℝ)|=(2625547789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704155659/5000000000 : ℝ)|^4915 ≤ (9201129481061/20000000000000 : ℝ)^3891
        have hw : |(2704155659/5000000000 : ℝ)|=(2704155659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393366993/2500000000 : ℝ)|^4915 ≤ (967150055923/10000000000000 : ℝ)^3891
        have hw : |(-393366993/2500000000 : ℝ)|=(393366993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_3 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4458384077/10000000000 : ℝ)*x 0 + (4055117709/10000000000 : ℝ)*x 1 + (4055117013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458384077/10000000000 : ℝ)^4915 ≤ (18022748479841/50000000000000 : ℝ)^3891 := by
    have hnat : (4458384077 : ℕ)^4915*50000000000000^3891 ≤ 18022748479841^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458384077 10000000000 18022748479841 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4055117709/10000000000 : ℝ)^4915 ≤ (3197725497959/10000000000000 : ℝ)^3891 := by
    have hnat : (4055117709 : ℕ)^4915*10000000000000^3891 ≤ 3197725497959^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4055117709 10000000000 3197725497959 10000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4055117013/10000000000 : ℝ)^4915 ≤ (31977248046781/100000000000000 : ℝ)^3891 := by
    have hnat : (4055117013 : ℕ)^4915*100000000000000^3891 ≤ 31977248046781^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4055117013 10000000000 31977248046781 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458384077/10000000000 : ℝ), (4055117709/10000000000 : ℝ), (4055117013/10000000000 : ℝ)] ![(18022748479841/50000000000000 : ℝ), (3197725497959/10000000000000 : ℝ), (31977248046781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458384077/10000000000 : ℝ)|^4915 ≤ (18022748479841/50000000000000 : ℝ)^3891
        have hw : |(4458384077/10000000000 : ℝ)|=(4458384077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4055117709/10000000000 : ℝ)|^4915 ≤ (3197725497959/10000000000000 : ℝ)^3891
        have hw : |(4055117709/10000000000 : ℝ)|=(4055117709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4055117013/10000000000 : ℝ)|^4915 ≤ (31977248046781/100000000000000 : ℝ)^3891
        have hw : |(4055117013/10000000000 : ℝ)|=(4055117013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_4 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-469946827/2500000000 : ℝ)*x 0 + (5215715909/10000000000 : ℝ)*x 1 + (1303928881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469946827/2500000000 : ℝ)^4915 ≤ (12108068557783/100000000000000 : ℝ)^3891 := by
    have hnat : (469946827 : ℕ)^4915*100000000000000^3891 ≤ 12108068557783^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469946827 2500000000 12108068557783 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215715909/10000000000 : ℝ)^4915 ≤ (43945967763027/100000000000000 : ℝ)^3891 := by
    have hnat : (5215715909 : ℕ)^4915*100000000000000^3891 ≤ 43945967763027^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215715909 10000000000 43945967763027 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303928881/2500000000 : ℝ)^4915 ≤ (274662272909/625000000000 : ℝ)^3891 := by
    have hnat : (1303928881 : ℕ)^4915*625000000000^3891 ≤ 274662272909^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303928881 2500000000 274662272909 625000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469946827/2500000000 : ℝ), (5215715909/10000000000 : ℝ), (1303928881/2500000000 : ℝ)] ![(12108068557783/100000000000000 : ℝ), (43945967763027/100000000000000 : ℝ), (274662272909/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469946827/2500000000 : ℝ)|^4915 ≤ (12108068557783/100000000000000 : ℝ)^3891
        have hw : |(-469946827/2500000000 : ℝ)|=(469946827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215715909/10000000000 : ℝ)|^4915 ≤ (43945967763027/100000000000000 : ℝ)^3891
        have hw : |(5215715909/10000000000 : ℝ)|=(5215715909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303928881/2500000000 : ℝ)|^4915 ≤ (274662272909/625000000000 : ℝ)^3891
        have hw : |(1303928881/2500000000 : ℝ)|=(1303928881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_5 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8613291/16000000 : ℝ)*x 0 + (-414007419/2500000000 : ℝ)*x 1 + (5215715781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8613291/16000000 : ℝ)^4915 ≤ (2858570937733/6250000000000 : ℝ)^3891 := by
    have hnat : (8613291 : ℕ)^4915*6250000000000^3891 ≤ 2858570937733^3891*16000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8613291 16000000 2858570937733 6250000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414007419/2500000000 : ℝ)^4915 ≤ (2579224643683/25000000000000 : ℝ)^3891 := by
    have hnat : (414007419 : ℕ)^4915*25000000000000^3891 ≤ 2579224643683^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414007419 2500000000 2579224643683 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215715781/10000000000 : ℝ)^4915 ≤ (5493245800089/12500000000000 : ℝ)^3891 := by
    have hnat : (5215715781 : ℕ)^4915*12500000000000^3891 ≤ 5493245800089^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215715781 10000000000 5493245800089 12500000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8613291/16000000 : ℝ), (-414007419/2500000000 : ℝ), (5215715781/10000000000 : ℝ)] ![(2858570937733/6250000000000 : ℝ), (2579224643683/25000000000000 : ℝ), (5493245800089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8613291/16000000 : ℝ)|^4915 ≤ (2858570937733/6250000000000 : ℝ)^3891
        have hw : |(8613291/16000000 : ℝ)|=(8613291/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414007419/2500000000 : ℝ)|^4915 ≤ (2579224643683/25000000000000 : ℝ)^3891
        have hw : |(-414007419/2500000000 : ℝ)|=(414007419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215715781/10000000000 : ℝ)|^4915 ≤ (5493245800089/12500000000000 : ℝ)^3891
        have hw : |(5215715781/10000000000 : ℝ)|=(5215715781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_6 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383306897/10000000000 : ℝ)*x 0 + (5215715737/10000000000 : ℝ)*x 1 + (-1656029707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383306897/10000000000 : ℝ)^4915 ≤ (45737135239833/100000000000000 : ℝ)^3891 := by
    have hnat : (5383306897 : ℕ)^4915*100000000000000^3891 ≤ 45737135239833^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383306897 10000000000 45737135239833 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215715737/10000000000 : ℝ)^4915 ≤ (43945965932417/100000000000000 : ℝ)^3891 := by
    have hnat : (5215715737 : ℕ)^4915*100000000000000^3891 ≤ 43945965932417^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215715737 10000000000 43945965932417 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1656029707/10000000000 : ℝ)^4915 ≤ (2579224704671/25000000000000 : ℝ)^3891 := by
    have hnat : (1656029707 : ℕ)^4915*25000000000000^3891 ≤ 2579224704671^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656029707 10000000000 2579224704671 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383306897/10000000000 : ℝ), (5215715737/10000000000 : ℝ), (-1656029707/10000000000 : ℝ)] ![(45737135239833/100000000000000 : ℝ), (43945965932417/100000000000000 : ℝ), (2579224704671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383306897/10000000000 : ℝ)|^4915 ≤ (45737135239833/100000000000000 : ℝ)^3891
        have hw : |(5383306897/10000000000 : ℝ)|=(5383306897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215715737/10000000000 : ℝ)|^4915 ≤ (43945965932417/100000000000000 : ℝ)^3891
        have hw : |(5215715737/10000000000 : ℝ)|=(5215715737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1656029707/10000000000 : ℝ)|^4915 ≤ (2579224704671/25000000000000 : ℝ)^3891
        have hw : |(-1656029707/10000000000 : ℝ)|=(1656029707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_7 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2436343/6250000 : ℝ)*x 0 + (1083727469/2500000000 : ℝ)*x 1 + (21674547/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2436343/6250000 : ℝ)^4915 ≤ (30421739280017/100000000000000 : ℝ)^3891 := by
    have hnat : (2436343 : ℕ)^4915*100000000000000^3891 ≤ 30421739280017^3891*6250000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436343 6250000 30421739280017 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083727469/2500000000 : ℝ)^4915 ≤ (34789132763391/100000000000000 : ℝ)^3891 := by
    have hnat : (1083727469 : ℕ)^4915*100000000000000^3891 ≤ 34789132763391^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083727469 2500000000 34789132763391 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21674547/50000000 : ℝ)^4915 ≤ (34789127937997/100000000000000 : ℝ)^3891 := by
    have hnat : (21674547 : ℕ)^4915*100000000000000^3891 ≤ 34789127937997^3891*50000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21674547 50000000 34789127937997 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2436343/6250000 : ℝ), (1083727469/2500000000 : ℝ), (21674547/50000000 : ℝ)] ![(30421739280017/100000000000000 : ℝ), (34789132763391/100000000000000 : ℝ), (34789127937997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2436343/6250000 : ℝ)|^4915 ≤ (30421739280017/100000000000000 : ℝ)^3891
        have hw : |(2436343/6250000 : ℝ)|=(2436343/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083727469/2500000000 : ℝ)|^4915 ≤ (34789132763391/100000000000000 : ℝ)^3891
        have hw : |(1083727469/2500000000 : ℝ)|=(1083727469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21674547/50000000 : ℝ)|^4915 ≤ (34789127937997/100000000000000 : ℝ)^3891
        have hw : |(21674547/50000000 : ℝ)|=(21674547/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_8 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-441829673/2500000000 : ℝ)*x 0 + (5077225061/10000000000 : ℝ)*x 1 + (5437779877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441829673/2500000000 : ℝ)^4915 ≤ (2240060000973/20000000000000 : ℝ)^3891 := by
    have hnat : (441829673 : ℕ)^4915*20000000000000^3891 ≤ 2240060000973^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441829673 2500000000 2240060000973 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077225061/10000000000 : ℝ)^4915 ≤ (10619295574341/25000000000000 : ℝ)^3891 := by
    have hnat : (5077225061 : ℕ)^4915*25000000000000^3891 ≤ 10619295574341^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077225061 10000000000 10619295574341 25000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437779877/10000000000 : ℝ)^4915 ≤ (1852900707403/4000000000000 : ℝ)^3891 := by
    have hnat : (5437779877 : ℕ)^4915*4000000000000^3891 ≤ 1852900707403^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437779877 10000000000 1852900707403 4000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441829673/2500000000 : ℝ), (5077225061/10000000000 : ℝ), (5437779877/10000000000 : ℝ)] ![(2240060000973/20000000000000 : ℝ), (10619295574341/25000000000000 : ℝ), (1852900707403/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441829673/2500000000 : ℝ)|^4915 ≤ (2240060000973/20000000000000 : ℝ)^3891
        have hw : |(-441829673/2500000000 : ℝ)|=(441829673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077225061/10000000000 : ℝ)|^4915 ≤ (10619295574341/25000000000000 : ℝ)^3891
        have hw : |(5077225061/10000000000 : ℝ)|=(5077225061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437779877/10000000000 : ℝ)|^4915 ≤ (1852900707403/4000000000000 : ℝ)^3891
        have hw : |(5437779877/10000000000 : ℝ)|=(5437779877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_9 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523086673/1000000000 : ℝ)*x 0 + (-195050749/1250000000 : ℝ)*x 1 + (169930639/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523086673/1000000000 : ℝ)^4915 ≤ (22053640390441/50000000000000 : ℝ)^3891 := by
    have hnat : (523086673 : ℕ)^4915*50000000000000^3891 ≤ 22053640390441^3891*1000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523086673 1000000000 22053640390441 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195050749/1250000000 : ℝ)^4915 ≤ (1914039076931/20000000000000 : ℝ)^3891 := by
    have hnat : (195050749 : ℕ)^4915*20000000000000^3891 ≤ 1914039076931^3891*1250000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195050749 1250000000 1914039076931 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169930639/312500000 : ℝ)^4915 ≤ (23161261914663/50000000000000 : ℝ)^3891 := by
    have hnat : (169930639 : ℕ)^4915*50000000000000^3891 ≤ 23161261914663^3891*312500000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169930639 312500000 23161261914663 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523086673/1000000000 : ℝ), (-195050749/1250000000 : ℝ), (169930639/312500000 : ℝ)] ![(22053640390441/50000000000000 : ℝ), (1914039076931/20000000000000 : ℝ), (23161261914663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523086673/1000000000 : ℝ)|^4915 ≤ (22053640390441/50000000000000 : ℝ)^3891
        have hw : |(523086673/1000000000 : ℝ)|=(523086673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195050749/1250000000 : ℝ)|^4915 ≤ (1914039076931/20000000000000 : ℝ)^3891
        have hw : |(-195050749/1250000000 : ℝ)|=(195050749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169930639/312500000 : ℝ)|^4915 ≤ (23161261914663/50000000000000 : ℝ)^3891
        have hw : |(169930639/312500000 : ℝ)|=(169930639/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_10 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230867123/10000000000 : ℝ)*x 0 + (2718890141/5000000000 : ℝ)*x 1 + (-780202841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230867123/10000000000 : ℝ)^4915 ≤ (5513410620851/12500000000000 : ℝ)^3891 := by
    have hnat : (5230867123 : ℕ)^4915*12500000000000^3891 ≤ 5513410620851^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230867123 10000000000 5513410620851 12500000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718890141/5000000000 : ℝ)^4915 ≤ (23161261021541/50000000000000 : ℝ)^3891 := by
    have hnat : (2718890141 : ℕ)^4915*50000000000000^3891 ≤ 23161261021541^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718890141 5000000000 23161261021541 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780202841/5000000000 : ℝ)^4915 ≤ (9570192983019/100000000000000 : ℝ)^3891 := by
    have hnat : (780202841 : ℕ)^4915*100000000000000^3891 ≤ 9570192983019^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780202841 5000000000 9570192983019 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230867123/10000000000 : ℝ), (2718890141/5000000000 : ℝ), (-780202841/5000000000 : ℝ)] ![(5513410620851/12500000000000 : ℝ), (23161261021541/50000000000000 : ℝ), (9570192983019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230867123/10000000000 : ℝ)|^4915 ≤ (5513410620851/12500000000000 : ℝ)^3891
        have hw : |(5230867123/10000000000 : ℝ)|=(5230867123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718890141/5000000000 : ℝ)|^4915 ≤ (23161261021541/50000000000000 : ℝ)^3891
        have hw : |(2718890141/5000000000 : ℝ)|=(2718890141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-780202841/5000000000 : ℝ)|^4915 ≤ (9570192983019/100000000000000 : ℝ)^3891
        have hw : |(-780202841/5000000000 : ℝ)|=(780202841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_11 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2270862291/5000000000 : ℝ)*x 0 + (4012230231/10000000000 : ℝ)*x 1 + (1003057387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2270862291/5000000000 : ℝ)^4915 ≤ (7379740646527/20000000000000 : ℝ)^3891 := by
    have hnat : (2270862291 : ℕ)^4915*20000000000000^3891 ≤ 7379740646527^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270862291 5000000000 7379740646527 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4012230231/10000000000 : ℝ)^4915 ≤ (6310130353691/20000000000000 : ℝ)^3891 := by
    have hnat : (4012230231 : ℕ)^4915*20000000000000^3891 ≤ 6310130353691^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012230231 10000000000 6310130353691 20000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003057387/2500000000 : ℝ)^4915 ≤ (31550644984149/100000000000000 : ℝ)^3891 := by
    have hnat : (1003057387 : ℕ)^4915*100000000000000^3891 ≤ 31550644984149^3891*2500000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003057387 2500000000 31550644984149 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2270862291/5000000000 : ℝ), (4012230231/10000000000 : ℝ), (1003057387/2500000000 : ℝ)] ![(7379740646527/20000000000000 : ℝ), (6310130353691/20000000000000 : ℝ), (31550644984149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2270862291/5000000000 : ℝ)|^4915 ≤ (7379740646527/20000000000000 : ℝ)^3891
        have hw : |(2270862291/5000000000 : ℝ)|=(2270862291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4012230231/10000000000 : ℝ)|^4915 ≤ (6310130353691/20000000000000 : ℝ)^3891
        have hw : |(4012230231/10000000000 : ℝ)|=(4012230231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003057387/2500000000 : ℝ)|^4915 ≤ (31550644984149/100000000000000 : ℝ)^3891
        have hw : |(1003057387/2500000000 : ℝ)|=(1003057387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_12 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1463213487/10000000000 : ℝ)*x 0 + (346343843/625000000 : ℝ)*x 1 + (5195893691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1463213487/10000000000 : ℝ)^4915 ≤ (882349279701/10000000000000 : ℝ)^3891 := by
    have hnat : (1463213487 : ℕ)^4915*10000000000000^3891 ≤ 882349279701^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463213487 10000000000 882349279701 10000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346343843/625000000 : ℝ)^4915 ≤ (23720701656437/50000000000000 : ℝ)^3891 := by
    have hnat : (346343843 : ℕ)^4915*50000000000000^3891 ≤ 23720701656437^3891*625000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346343843 625000000 23720701656437 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195893691/10000000000 : ℝ)^4915 ≤ (43735103879429/100000000000000 : ℝ)^3891 := by
    have hnat : (5195893691 : ℕ)^4915*100000000000000^3891 ≤ 43735103879429^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195893691 10000000000 43735103879429 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1463213487/10000000000 : ℝ), (346343843/625000000 : ℝ), (5195893691/10000000000 : ℝ)] ![(882349279701/10000000000000 : ℝ), (23720701656437/50000000000000 : ℝ), (43735103879429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1463213487/10000000000 : ℝ)|^4915 ≤ (882349279701/10000000000000 : ℝ)^3891
        have hw : |(-1463213487/10000000000 : ℝ)|=(1463213487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346343843/625000000 : ℝ)|^4915 ≤ (23720701656437/50000000000000 : ℝ)^3891
        have hw : |(346343843/625000000 : ℝ)|=(346343843/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195893691/10000000000 : ℝ)|^4915 ≤ (43735103879429/100000000000000 : ℝ)^3891
        have hw : |(5195893691/10000000000 : ℝ)|=(5195893691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_13 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396923839/10000000000 : ℝ)*x 0 + (-1664242401/10000000000 : ℝ)*x 1 + (5195894121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396923839/10000000000 : ℝ)^4915 ≤ (45883321358947/100000000000000 : ℝ)^3891 := by
    have hnat : (5396923839 : ℕ)^4915*100000000000000^3891 ≤ 45883321358947^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396923839 10000000000 45883321358947 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1664242401/10000000000 : ℝ)^4915 ≤ (648848135771/6250000000000 : ℝ)^3891 := by
    have hnat : (1664242401 : ℕ)^4915*6250000000000^3891 ≤ 648848135771^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664242401 10000000000 648848135771 6250000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195894121/10000000000 : ℝ)^4915 ≤ (43735108451371/100000000000000 : ℝ)^3891 := by
    have hnat : (5195894121 : ℕ)^4915*100000000000000^3891 ≤ 43735108451371^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195894121 10000000000 43735108451371 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396923839/10000000000 : ℝ), (-1664242401/10000000000 : ℝ), (5195894121/10000000000 : ℝ)] ![(45883321358947/100000000000000 : ℝ), (648848135771/6250000000000 : ℝ), (43735108451371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396923839/10000000000 : ℝ)|^4915 ≤ (45883321358947/100000000000000 : ℝ)^3891
        have hw : |(5396923839/10000000000 : ℝ)|=(5396923839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1664242401/10000000000 : ℝ)|^4915 ≤ (648848135771/6250000000000 : ℝ)^3891
        have hw : |(-1664242401/10000000000 : ℝ)|=(1664242401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195894121/10000000000 : ℝ)|^4915 ≤ (43735108451371/100000000000000 : ℝ)^3891
        have hw : |(5195894121/10000000000 : ℝ)|=(5195894121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_14 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396923251/10000000000 : ℝ)*x 0 + (5195894403/10000000000 : ℝ)*x 1 + (-1664242823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396923251/10000000000 : ℝ)^4915 ≤ (45883315044313/100000000000000 : ℝ)^3891 := by
    have hnat : (5396923251 : ℕ)^4915*100000000000000^3891 ≤ 45883315044313^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396923251 10000000000 45883315044313 100000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195894403/10000000000 : ℝ)^4915 ≤ (21867555724857/50000000000000 : ℝ)^3891 := by
    have hnat : (5195894403 : ℕ)^4915*50000000000000^3891 ≤ 21867555724857^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195894403 10000000000 21867555724857 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1664242823/10000000000 : ℝ)^4915 ≤ (5190786748781/50000000000000 : ℝ)^3891 := by
    have hnat : (1664242823 : ℕ)^4915*50000000000000^3891 ≤ 5190786748781^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664242823 10000000000 5190786748781 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396923251/10000000000 : ℝ), (5195894403/10000000000 : ℝ), (-1664242823/10000000000 : ℝ)] ![(45883315044313/100000000000000 : ℝ), (21867555724857/50000000000000 : ℝ), (5190786748781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396923251/10000000000 : ℝ)|^4915 ≤ (45883315044313/100000000000000 : ℝ)^3891
        have hw : |(5396923251/10000000000 : ℝ)|=(5396923251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195894403/10000000000 : ℝ)|^4915 ≤ (21867555724857/50000000000000 : ℝ)^3891
        have hw : |(5195894403/10000000000 : ℝ)|=(5195894403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1664242823/10000000000 : ℝ)|^4915 ≤ (5190786748781/50000000000000 : ℝ)^3891
        have hw : |(-1664242823/10000000000 : ℝ)|=(1664242823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1649_box_15 (p : ℝ) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3838861557/10000000000 : ℝ)*x 0 + (2181826203/5000000000 : ℝ)*x 1 + (4363654171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3838861557/10000000000 : ℝ)^4915 ≤ (14919230452427/50000000000000 : ℝ)^3891 := by
    have hnat : (3838861557 : ℕ)^4915*50000000000000^3891 ≤ 14919230452427^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3838861557 10000000000 14919230452427 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181826203/5000000000 : ℝ)^4915 ≤ (17540380289959/50000000000000 : ℝ)^3891 := by
    have hnat : (2181826203 : ℕ)^4915*50000000000000^3891 ≤ 17540380289959^3891*5000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181826203 5000000000 17540380289959 50000000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4363654171/10000000000 : ℝ)^4915 ≤ (4385097312943/12500000000000 : ℝ)^3891 := by
    have hnat : (4363654171 : ℕ)^4915*12500000000000^3891 ≤ 4385097312943^3891*10000000000^4915 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363654171 10000000000 4385097312943 12500000000000 4915 3891 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4915/1024 : ℝ)) 4915 3891 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3838861557/10000000000 : ℝ), (2181826203/5000000000 : ℝ), (4363654171/10000000000 : ℝ)] ![(14919230452427/50000000000000 : ℝ), (17540380289959/50000000000000 : ℝ), (4385097312943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3838861557/10000000000 : ℝ)|^4915 ≤ (14919230452427/50000000000000 : ℝ)^3891
        have hw : |(3838861557/10000000000 : ℝ)|=(3838861557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2181826203/5000000000 : ℝ)|^4915 ≤ (17540380289959/50000000000000 : ℝ)^3891
        have hw : |(2181826203/5000000000 : ℝ)|=(2181826203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4363654171/10000000000 : ℝ)|^4915 ≤ (4385097312943/12500000000000 : ℝ)^3891
        have hw : |(4363654171/10000000000 : ℝ)|=(4363654171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1649_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1627/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2133/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65063/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11723/20000 : ℝ) ∧ (40589/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44107/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1627/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2133/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1627/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2133/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1627/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2133/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1627/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2133/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1627/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2133/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1627/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2133/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2133/20000 : ℝ) ^ (4911/1024 : ℝ) ≤ (2178707890439393/100000000000000000000 : ℝ) := by
    have hpowers : (2133/20000 : ℝ)^4911 ≤ (2178707890439393/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2133 : ℕ)^4911*100000000000000000000^1024 ≤ 2178707890439393^1024*20000^4911 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2133 20000 2178707890439393 100000000000000000000 4911 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2133/20000 : ℝ)) (X := (2178707890439393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1627/10000 : ℝ) ^ (4911/1024 : ℝ) ≤ (8257808393161483/50000000000000000000 : ℝ) := by
    have hpowers : (1627/10000 : ℝ)^4911 ≤ (8257808393161483/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1627 : ℕ)^4911*50000000000000000000^1024 ≤ 8257808393161483^1024*10000^4911 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1627 10000 8257808393161483 50000000000000000000 4911 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1627/10000 : ℝ)) (X := (8257808393161483/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002178707890439393/50000000000000000000 : ℝ) ≤ (400003634222617/400000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (50002178707890439393/50000000000000000000 : ℝ)^1024 ≤ (400003634222617/400000000000000 : ℝ)^4911 := by
      have hnat : (50002178707890439393 : ℕ)^1024*400000000000000^4911 ≤ 400003634222617^4911*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002178707890439393 50000000000000000000 400003634222617 400000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003634222617/400000000000000 : ℝ)) (X := (50002178707890439393/50000000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018694324676762359/100000000000000000000 : ℝ) ≤ (10000389769342211/10000000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (100018694324676762359/100000000000000000000 : ℝ)^1024 ≤ (10000389769342211/10000000000000000 : ℝ)^4911 := by
      have hnat : (100018694324676762359 : ℕ)^1024*10000000000000000^4911 ≤ 10000389769342211^4911*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018694324676762359 100000000000000000000 10000389769342211 10000000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000389769342211/10000000000000000 : ℝ)) (X := (100018694324676762359/100000000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008257808393161483/25000000000000000000 : ℝ) ≤ (10000688683118997/10000000000000000 : ℝ) ^ (4911/1024 : ℝ) := by
    have hpowers : (25008257808393161483/25000000000000000000 : ℝ)^1024 ≤ (10000688683118997/10000000000000000 : ℝ)^4911 := by
      have hnat : (25008257808393161483 : ℕ)^1024*10000000000000000^4911 ≤ 10000688683118997^4911*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008257808393161483 25000000000000000000 10000688683118997 10000000000000000 1024 4911 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000688683118997/10000000000000000 : ℝ)) (X := (25008257808393161483/25000000000000000000 : ℝ)) (by norm_num) 4911 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2178707890439393/100000000000000000000 : ℝ) ≤ ((11208826682917072349/11210000000000000000 : ℝ)+2*(149456888393/280250000000000 : ℝ)*(2133/20000 : ℝ))^(4911/1024 : ℝ) := by
    rw [show (11208826682917072349/11210000000000000000 : ℝ)+2*(149456888393/280250000000000 : ℝ)*(2133/20000 : ℝ)=(400003634222617/400000000000000 : ℝ) by norm_num, show 1+2*(2178707890439393/100000000000000000000 : ℝ)=(50002178707890439393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8257808393161483/50000000000000000000 : ℝ)+(2178707890439393/100000000000000000000 : ℝ) ≤ ((11208826682917072349/11210000000000000000 : ℝ)+(149456888393/280250000000000 : ℝ)*((1627/10000 : ℝ)+(2133/20000 : ℝ)))^(4911/1024 : ℝ) := by
    rw [show (11208826682917072349/11210000000000000000 : ℝ)+(149456888393/280250000000000 : ℝ)*((1627/10000 : ℝ)+(2133/20000 : ℝ))=(10000389769342211/10000000000000000 : ℝ) by norm_num, show 1+(8257808393161483/50000000000000000000 : ℝ)+(2178707890439393/100000000000000000000 : ℝ)=(100018694324676762359/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8257808393161483/50000000000000000000 : ℝ) ≤ ((11208826682917072349/11210000000000000000 : ℝ)+2*(149456888393/280250000000000 : ℝ)*(1627/10000 : ℝ))^(4911/1024 : ℝ) := by
    rw [show (11208826682917072349/11210000000000000000 : ℝ)+2*(149456888393/280250000000000 : ℝ)*(1627/10000 : ℝ)=(10000688683118997/10000000000000000 : ℝ) by norm_num, show 1+2*(8257808393161483/50000000000000000000 : ℝ)=(25008257808393161483/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11208826682917072349/11210000000000000000 : ℝ)*(X 1 0+X 2 0)+(149456888393/280250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (2133/20000 : ℝ)) (hi := (1627/10000 : ℝ)) (c := (11208826682917072349/11210000000000000000 : ℝ)) (alpha := (149456888393/280250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11208826682917072349/11210000000000000000 : ℝ)*(X 0 1+X 2 1)+(149456888393/280250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (2133/20000 : ℝ)) (hi := (1627/10000 : ℝ)) (c := (11208826682917072349/11210000000000000000 : ℝ)) (alpha := (149456888393/280250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11208826682917072349/11210000000000000000 : ℝ)*(X 0 2+X 1 2)+(149456888393/280250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4911/1024 : ℝ)) (lo := (2133/20000 : ℝ)) (hi := (1627/10000 : ℝ)) (c := (11208826682917072349/11210000000000000000 : ℝ)) (alpha := (149456888393/280250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1352497669/10000000000 : ℝ)*X 0 0+(338019481/625000000 : ℝ)*X 0 1+(216332431/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625548021/5000000000 : ℝ)*X 1 0+(-1573467831/10000000000 : ℝ)*X 1 1+(67603887/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625547789/5000000000 : ℝ)*X 2 0+(2704155659/5000000000 : ℝ)*X 2 1+(-393366993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4458384077/10000000000 : ℝ)*X 0 0+(4055117709/10000000000 : ℝ)*X 0 1+(4055117013/10000000000 : ℝ)*X 0 2+(4458384077/10000000000 : ℝ)*X 1 0+(4055117709/10000000000 : ℝ)*X 1 1+(4055117013/10000000000 : ℝ)*X 1 2+(4458384077/10000000000 : ℝ)*X 2 0+(4055117709/10000000000 : ℝ)*X 2 1+(4055117013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-469946827/2500000000 : ℝ)*X 0 0+(5215715909/10000000000 : ℝ)*X 0 1+(1303928881/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8613291/16000000 : ℝ)*X 1 0+(-414007419/2500000000 : ℝ)*X 1 1+(5215715781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5383306897/10000000000 : ℝ)*X 2 0+(5215715737/10000000000 : ℝ)*X 2 1+(-1656029707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2436343/6250000 : ℝ)*X 0 0+(1083727469/2500000000 : ℝ)*X 0 1+(21674547/50000000 : ℝ)*X 0 2+(2436343/6250000 : ℝ)*X 1 0+(1083727469/2500000000 : ℝ)*X 1 1+(21674547/50000000 : ℝ)*X 1 2+(2436343/6250000 : ℝ)*X 2 0+(1083727469/2500000000 : ℝ)*X 2 1+(21674547/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-441829673/2500000000 : ℝ)*X 0 0+(5077225061/10000000000 : ℝ)*X 0 1+(5437779877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((523086673/1000000000 : ℝ)*X 1 0+(-195050749/1250000000 : ℝ)*X 1 1+(169930639/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230867123/10000000000 : ℝ)*X 2 0+(2718890141/5000000000 : ℝ)*X 2 1+(-780202841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2270862291/5000000000 : ℝ)*X 0 0+(4012230231/10000000000 : ℝ)*X 0 1+(1003057387/2500000000 : ℝ)*X 0 2+(2270862291/5000000000 : ℝ)*X 1 0+(4012230231/10000000000 : ℝ)*X 1 1+(1003057387/2500000000 : ℝ)*X 1 2+(2270862291/5000000000 : ℝ)*X 2 0+(4012230231/10000000000 : ℝ)*X 2 1+(1003057387/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1463213487/10000000000 : ℝ)*X 0 0+(346343843/625000000 : ℝ)*X 0 1+(5195893691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396923839/10000000000 : ℝ)*X 1 0+(-1664242401/10000000000 : ℝ)*X 1 1+(5195894121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5396923251/10000000000 : ℝ)*X 2 0+(5195894403/10000000000 : ℝ)*X 2 1+(-1664242823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3838861557/10000000000 : ℝ)*X 0 0+(2181826203/5000000000 : ℝ)*X 0 1+(4363654171/10000000000 : ℝ)*X 0 2+(3838861557/10000000000 : ℝ)*X 1 0+(2181826203/5000000000 : ℝ)*X 1 1+(4363654171/10000000000 : ℝ)*X 1 2+(3838861557/10000000000 : ℝ)*X 2 0+(2181826203/5000000000 : ℝ)*X 2 1+(4363654171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1649_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65063/100000 : ℝ) ≤ (-91166573151187443249397611013629/140125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28409391/100000000000000 : ℝ)*(lower0) + (12317189/100000000000000 : ℝ)*(lower2) + (822341/25000000000000 : ℝ)*(lower4) + (28310003/100000000000000 : ℝ)*(lower5) + (439258809016031/25000000000000 : ℝ)*(major0) + (439258809016031/25000000000000 : ℝ)*(major1) + (439258809016031/25000000000000 : ℝ)*(major2) + (257636823/100000000000000 : ℝ)*(sp1) + (511052720834791/20000000000000 : ℝ)*(sp4) + (319408315906379/12500000000000 : ℝ)*(sp5) + (511053356977571/20000000000000 : ℝ)*(sp6) + (122561116918401/12500000000000 : ℝ)*(sp7) + (31807139/1000000000000 : ℝ)*(sp8) + (1715473599/100000000000000 : ℝ)*(sp15) + (980490650820807/100000000000000 : ℝ)*(f.failure) + (511053356977571/20000000000000 : ℝ)*(f.sum) + (319141592188889/28025000000000000000000000000 : ℝ)*base65 + (2868537580454103181/280250000000000000000000000000000 : ℝ)*base68 + (1405296547252103181/280250000000000000000000000000000 : ℝ)*base70 + (647340597367103181/280250000000000000000000000000000 : ℝ)*base72 + (199270091591961/28025000000000000000000000000 : ℝ)*base74 + (1258795397900103181/280250000000000000000000000000000 : ℝ)*base76 + (156296739779353181/280250000000000000000000000000000 : ℝ)*base78 + (2379690818689103181/280250000000000000000000000000000 : ℝ)*base80 + (288203267483/3503125000000000000000000000 : ℝ)*base81 + (28689937/10000000000000000000000 : ℝ)*base89 + (28689937/10000000000000000000000 : ℝ)*base91 + (28689937/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11723/20000 : ℝ) ≤ (6571013098222725363933168809673/11210000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4282369/25000000000000 : ℝ)*(lower1) + (3335371/25000000000000 : ℝ)*(upper2) + (11947093/50000000000000 : ℝ)*(upper3) + (170552131/100000000000000 : ℝ)*(lower5) + (36946122401253/2000000000000 : ℝ)*(major0) + (36946122401253/2000000000000 : ℝ)*(major1) + (36946122401253/2000000000000 : ℝ)*(major2) + (2644205277359319/100000000000000 : ℝ)*(sp0) + (661051989039959/25000000000000 : ℝ)*(sp1) + (41315620083243/1562500000000 : ℝ)*(sp2) + (1030859154800247/100000000000000 : ℝ)*(sp3) + (2067708071/25000000000000 : ℝ)*(sp6) + (374264057/6250000000000 : ℝ)*(sp7) + (2678800517/100000000000000 : ℝ)*(sp8) + (1030865143025159/100000000000000 : ℝ)*(f.failure) + (661051989039959/25000000000000 : ℝ)*(f.sum) + (338617445437/70062500000000000000000000 : ℝ)*base65 + (192307464015906703/22420000000000000000000000000000 : ℝ)*base68 + (141305933454486703/22420000000000000000000000000000 : ℝ)*base70 + (142682702742606703/22420000000000000000000000000000 : ℝ)*base72 + (1451794719117/1121000000000000000000000000 : ℝ)*base73 + (280678606275406703/22420000000000000000000000000000 : ℝ)*base76 + (4514042617246703/22420000000000000000000000000000 : ℝ)*base78 + (248151991060766703/22420000000000000000000000000000 : ℝ)*base80 + (1669495664443/1121000000000000000000000000 : ℝ)*base82 + (4490031/10000000000000000000000 : ℝ)*base90 + (4490031/10000000000000000000000 : ℝ)*base92 + (4490031/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40589/50000 : ℝ) ≤ (56877299469465738106499376813489/70062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7254763/100000000000000 : ℝ)*(lower3) + (35868457/25000000000000 : ℝ)*(upper4) + (17568101/100000000000000 : ℝ)*(lower5) + (242773743573287/12500000000000 : ℝ)*(major0) + (242773743573287/12500000000000 : ℝ)*(major1) + (242773743573287/12500000000000 : ℝ)*(major2) + (19660283/50000000000000 : ℝ)*(sp0) + (56240481111/100000000000000 : ℝ)*(sp1) + (73285712513/100000000000000 : ℝ)*(sp2) + (3307570427/20000000000000 : ℝ)*(sp3) + (173344110099277/6250000000000 : ℝ)*(sp8) + (1386724780213943/50000000000000 : ℝ)*(sp9) + (1386716257598243/50000000000000 : ℝ)*(sp10) + (33868665345177/3125000000000 : ℝ)*(sp11) + (1083813828897799/100000000000000 : ℝ)*(f.failure) + (1386752900454499/50000000000000 : ℝ)*(f.sum) + (15890245216469/28025000000000000000000000000 : ℝ)*base66 + (565481196078993837/140125000000000000000000000000000 : ℝ)*base68 + (207458003233243837/140125000000000000000000000000000 : ℝ)*base70 + (455427390588756163/140125000000000000000000000000000 : ℝ)*base71 + (19853767655997/14012500000000000000000000000 : ℝ)*base74 + (431992909410006163/140125000000000000000000000000000 : ℝ)*base75 + (736560193642493837/140125000000000000000000000000000 : ℝ)*base78 + (1065640133911243837/140125000000000000000000000000000 : ℝ)*base80 + (103648982794181/28025000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (38399791/10000000000000000000000 : ℝ)*base90 + (38399791/10000000000000000000000 : ℝ)*base92 + (38399791/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-44107/50000 : ℝ) ≤ (-6180300582821978657205181139109/7006250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2668281/3125000000000 : ℝ)*(lower1) + (203798267/100000000000000 : ℝ)*(lower4) + (1055087/12500000000000 : ℝ)*(upper5) + (49655572190503/2500000000000 : ℝ)*(major0) + (49655572190503/2500000000000 : ℝ)*(major1) + (49655572190503/2500000000000 : ℝ)*(major2) + (4441915999/100000000000000 : ℝ)*(sp0) + (6977207911/25000000000000 : ℝ)*(sp5) + (13158066737/25000000000000 : ℝ)*(sp6) + (7786587481/25000000000000 : ℝ)*(sp7) + (1446729622592957/50000000000000 : ℝ)*(sp12) + (723358944567567/25000000000000 : ℝ)*(sp13) + (578682210966993/20000000000000 : ℝ)*(sp14) + (554177345608017/50000000000000 : ℝ)*(sp15) + (1108385837565957/100000000000000 : ℝ)*(f.failure) + (361682960887739/12500000000000 : ℝ)*(f.sum) + (28466394389981/5605000000000000000000000000 : ℝ)*base66 + (23733367652238453/28025000000000000000000000000000 : ℝ)*base68 + (194675488565463453/28025000000000000000000000000000 : ℝ)*base70 + (107022992978388453/28025000000000000000000000000000 : ℝ)*base72 + (88997664919/87578125000000000000000000 : ℝ)*base74 + (135402664565711547/28025000000000000000000000000000 : ℝ)*base75 + (235179642615863453/28025000000000000000000000000000 : ℝ)*base78 + (194458787663113453/28025000000000000000000000000000 : ℝ)*base80 + (12062606862851/5605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (70076413/10000000000000000000000 : ℝ)*base90 + (70076413/10000000000000000000000 : ℝ)*base92 + (70076413/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1649_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1627/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2133/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65063/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11723/20000 : ℝ) else (40589/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44107/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1649_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1649_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65063/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11723/20000 : ℝ) else (40589/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44107/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1649_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1649_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1649_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4911/1024 : ℝ) ≤ p) (hpb : p ≤ (4915/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179199591/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65063/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11723/20000 : ℝ) else (40589/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44107/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1649_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
