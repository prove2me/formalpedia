-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1292_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:55.08116+00:00
-- url     : https://prove2.me/submissions/677b0f6f-f37a-48f2-ace8-3c8c5a86588d

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
theorem support_rectangle_w1292_s6_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087962027/10000000000 : ℝ)*x 0 + (84614393/156250000 : ℝ)*x 1 + (20971623/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087962027/10000000000 : ℝ)^1063 ≤ (12703461662807/100000000000000 : ℝ)^807 := by
    have hnat : (2087962027 : ℕ)^1063*100000000000000^807 ≤ 12703461662807^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087962027 10000000000 12703461662807 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84614393/156250000 : ℝ)^1063 ≤ (22289142138017/50000000000000 : ℝ)^807 := by
    have hnat : (84614393 : ℕ)^1063*50000000000000^807 ≤ 22289142138017^807*156250000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84614393 156250000 22289142138017 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20971623/40000000 : ℝ)^1063 ≤ (427182540471/1000000000000 : ℝ)^807 := by
    have hnat : (20971623 : ℕ)^1063*1000000000000^807 ≤ 427182540471^807*40000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20971623 40000000 427182540471 1000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087962027/10000000000 : ℝ), (84614393/156250000 : ℝ), (20971623/40000000 : ℝ)] ![(12703461662807/100000000000000 : ℝ), (22289142138017/50000000000000 : ℝ), (427182540471/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087962027/10000000000 : ℝ)|^1063 ≤ (12703461662807/100000000000000 : ℝ)^807
        have hw : |(-2087962027/10000000000 : ℝ)|=(2087962027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84614393/156250000 : ℝ)|^1063 ≤ (22289142138017/50000000000000 : ℝ)^807
        have hw : |(84614393/156250000 : ℝ)|=(84614393/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20971623/40000000 : ℝ)|^1063 ≤ (427182540471/1000000000000 : ℝ)^807
        have hw : |(20971623/40000000 : ℝ)|=(20971623/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337451639/2500000000 : ℝ)*x 0 + (-1087925891/5000000000 : ℝ)*x 1 + (1310726443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337451639/2500000000 : ℝ)^1063 ≤ (10967315265713/25000000000000 : ℝ)^807 := by
    have hnat : (1337451639 : ℕ)^1063*25000000000000^807 ≤ 10967315265713^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337451639 2500000000 10967315265713 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087925891/5000000000 : ℝ)^1063 ≤ (6706242315199/50000000000000 : ℝ)^807 := by
    have hnat : (1087925891 : ℕ)^1063*50000000000000^807 ≤ 6706242315199^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087925891 5000000000 6706242315199 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310726443/2500000000 : ℝ)^1063 ≤ (8543650856643/20000000000000 : ℝ)^807 := by
    have hnat : (1310726443 : ℕ)^1063*20000000000000^807 ≤ 8543650856643^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310726443 2500000000 8543650856643 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337451639/2500000000 : ℝ), (-1087925891/5000000000 : ℝ), (1310726443/2500000000 : ℝ)] ![(10967315265713/25000000000000 : ℝ), (6706242315199/50000000000000 : ℝ), (8543650856643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337451639/2500000000 : ℝ)|^1063 ≤ (10967315265713/25000000000000 : ℝ)^807
        have hw : |(1337451639/2500000000 : ℝ)|=(1337451639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087925891/5000000000 : ℝ)|^1063 ≤ (6706242315199/50000000000000 : ℝ)^807
        have hw : |(-1087925891/5000000000 : ℝ)|=(1087925891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310726443/2500000000 : ℝ)|^1063 ≤ (8543650856643/20000000000000 : ℝ)^807
        have hw : |(1310726443/2500000000 : ℝ)|=(1310726443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534980651/1000000000 : ℝ)*x 0 + (81920403/156250000 : ℝ)*x 1 + (-1087925909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534980651/1000000000 : ℝ)^1063 ≤ (8773852113197/20000000000000 : ℝ)^807 := by
    have hnat : (534980651 : ℕ)^1063*20000000000000^807 ≤ 8773852113197^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534980651 1000000000 8773852113197 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81920403/156250000 : ℝ)^1063 ≤ (8543650899573/20000000000000 : ℝ)^807 := by
    have hnat : (81920403 : ℕ)^1063*20000000000000^807 ≤ 8543650899573^807*156250000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81920403 156250000 8543650899573 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087925909/5000000000 : ℝ)^1063 ≤ (13412484922707/100000000000000 : ℝ)^807 := by
    have hnat : (1087925909 : ℕ)^1063*100000000000000^807 ≤ 13412484922707^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087925909 5000000000 13412484922707 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534980651/1000000000 : ℝ), (81920403/156250000 : ℝ), (-1087925909/5000000000 : ℝ)] ![(8773852113197/20000000000000 : ℝ), (8543650899573/20000000000000 : ℝ), (13412484922707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534980651/1000000000 : ℝ)|^1063 ≤ (8773852113197/20000000000000 : ℝ)^807
        have hw : |(534980651/1000000000 : ℝ)|=(534980651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81920403/156250000 : ℝ)|^1063 ≤ (8543650899573/20000000000000 : ℝ)^807
        have hw : |(81920403/156250000 : ℝ)|=(81920403/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087925909/5000000000 : ℝ)|^1063 ≤ (13412484922707/100000000000000 : ℝ)^807
        have hw : |(-1087925909/5000000000 : ℝ)|=(1087925909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2169930359/5000000000 : ℝ)*x 0 + (266633/640000 : ℝ)*x 1 + (4520495093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169930359/5000000000 : ℝ)^1063 ≤ (33302306069997/100000000000000 : ℝ)^807 := by
    have hnat : (2169930359 : ℕ)^1063*100000000000000^807 ≤ 33302306069997^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169930359 5000000000 33302306069997 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266633/640000 : ℝ)^1063 ≤ (6311524700119/20000000000000 : ℝ)^807 := by
    have hnat : (266633 : ℕ)^1063*20000000000000^807 ≤ 6311524700119^807*640000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266633 640000 6311524700119 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520495093/10000000000 : ℝ)^1063 ≤ (8785017602843/25000000000000 : ℝ)^807 := by
    have hnat : (4520495093 : ℕ)^1063*25000000000000^807 ≤ 8785017602843^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520495093 10000000000 8785017602843 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169930359/5000000000 : ℝ), (266633/640000 : ℝ), (4520495093/10000000000 : ℝ)] ![(33302306069997/100000000000000 : ℝ), (6311524700119/20000000000000 : ℝ), (8785017602843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169930359/5000000000 : ℝ)|^1063 ≤ (33302306069997/100000000000000 : ℝ)^807
        have hw : |(2169930359/5000000000 : ℝ)|=(2169930359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(266633/640000 : ℝ)|^1063 ≤ (6311524700119/20000000000000 : ℝ)^807
        have hw : |(266633/640000 : ℝ)|=(266633/640000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520495093/10000000000 : ℝ)|^1063 ≤ (8785017602843/25000000000000 : ℝ)^807
        have hw : |(4520495093/10000000000 : ℝ)|=(4520495093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-521993699/2500000000 : ℝ)*x 0 + (5243520827/10000000000 : ℝ)*x 1 + (338418931/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521993699/2500000000 : ℝ)^1063 ≤ (12703563995999/100000000000000 : ℝ)^807 := by
    have hnat : (521993699 : ℕ)^1063*100000000000000^807 ≤ 12703563995999^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521993699 2500000000 12703563995999 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243520827/10000000000 : ℝ)^1063 ≤ (42724855488033/100000000000000 : ℝ)^807 := by
    have hnat : (5243520827 : ℕ)^1063*100000000000000^807 ≤ 42724855488033^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243520827 10000000000 42724855488033 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338418931/625000000 : ℝ)^1063 ≤ (44571580502463/100000000000000 : ℝ)^807 := by
    have hnat : (338418931 : ℕ)^1063*100000000000000^807 ≤ 44571580502463^807*625000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338418931 625000000 44571580502463 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521993699/2500000000 : ℝ), (5243520827/10000000000 : ℝ), (338418931/625000000 : ℝ)] ![(12703563995999/100000000000000 : ℝ), (42724855488033/100000000000000 : ℝ), (44571580502463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521993699/2500000000 : ℝ)|^1063 ≤ (12703563995999/100000000000000 : ℝ)^807
        have hw : |(-521993699/2500000000 : ℝ)|=(521993699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243520827/10000000000 : ℝ)|^1063 ≤ (42724855488033/100000000000000 : ℝ)^807
        have hw : |(5243520827/10000000000 : ℝ)|=(5243520827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338418931/625000000 : ℝ)|^1063 ≤ (44571580502463/100000000000000 : ℝ)^807
        have hw : |(338418931/625000000 : ℝ)|=(338418931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305663803/10000000000 : ℝ)*x 0 + (-2004054753/10000000000 : ℝ)*x 1 + (338418927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305663803/10000000000 : ℝ)^1063 ≤ (43393080618351/100000000000000 : ℝ)^807 := by
    have hnat : (5305663803 : ℕ)^1063*100000000000000^807 ≤ 43393080618351^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305663803 10000000000 43393080618351 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004054753/10000000000 : ℝ)^1063 ≤ (3008834888419/25000000000000 : ℝ)^807 := by
    have hnat : (2004054753 : ℕ)^1063*25000000000000^807 ≤ 3008834888419^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004054753 10000000000 3008834888419 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338418927/625000000 : ℝ)^1063 ≤ (44571579808521/100000000000000 : ℝ)^807 := by
    have hnat : (338418927 : ℕ)^1063*100000000000000^807 ≤ 44571579808521^807*625000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338418927 625000000 44571579808521 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305663803/10000000000 : ℝ), (-2004054753/10000000000 : ℝ), (338418927/625000000 : ℝ)] ![(43393080618351/100000000000000 : ℝ), (3008834888419/25000000000000 : ℝ), (44571579808521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305663803/10000000000 : ℝ)|^1063 ≤ (43393080618351/100000000000000 : ℝ)^807
        have hw : |(5305663803/10000000000 : ℝ)|=(5305663803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004054753/10000000000 : ℝ)|^1063 ≤ (3008834888419/25000000000000 : ℝ)^807
        have hw : |(-2004054753/10000000000 : ℝ)|=(2004054753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338418927/625000000 : ℝ)|^1063 ≤ (44571579808521/100000000000000 : ℝ)^807
        have hw : |(338418927/625000000 : ℝ)|=(338418927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305663833/10000000000 : ℝ)*x 0 + (5414702769/10000000000 : ℝ)*x 1 + (-5010137/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305663833/10000000000 : ℝ)^1063 ≤ (5424135117693/12500000000000 : ℝ)^807 := by
    have hnat : (5305663833 : ℕ)^1063*12500000000000^807 ≤ 5424135117693^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305663833 10000000000 5424135117693 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414702769/10000000000 : ℝ)^1063 ≤ (22285789562711/50000000000000 : ℝ)^807 := by
    have hnat : (5414702769 : ℕ)^1063*50000000000000^807 ≤ 22285789562711^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414702769 10000000000 22285789562711 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5010137/25000000 : ℝ)^1063 ≤ (6017669962737/50000000000000 : ℝ)^807 := by
    have hnat : (5010137 : ℕ)^1063*50000000000000^807 ≤ 6017669962737^807*25000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010137 25000000 6017669962737 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305663833/10000000000 : ℝ), (5414702769/10000000000 : ℝ), (-5010137/25000000 : ℝ)] ![(5424135117693/12500000000000 : ℝ), (22285789562711/50000000000000 : ℝ), (6017669962737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305663833/10000000000 : ℝ)|^1063 ≤ (5424135117693/12500000000000 : ℝ)^807
        have hw : |(5305663833/10000000000 : ℝ)|=(5305663833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414702769/10000000000 : ℝ)|^1063 ≤ (22285789562711/50000000000000 : ℝ)^807
        have hw : |(5414702769/10000000000 : ℝ)|=(5414702769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5010137/25000000 : ℝ)|^1063 ≤ (6017669962737/50000000000000 : ℝ)^807
        have hw : |(-5010137/25000000 : ℝ)|=(5010137/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s6_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4339886949/10000000000 : ℝ)*x 0 + (1129807713/2500000000 : ℝ)*x 1 + (208370567/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339886949/10000000000 : ℝ)^1063 ≤ (33302571208933/100000000000000 : ℝ)^807 := by
    have hnat : (4339886949 : ℕ)^1063*100000000000000^807 ≤ 33302571208933^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339886949 10000000000 33302571208933 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129807713/2500000000 : ℝ)^1063 ≤ (35127125861317/100000000000000 : ℝ)^807 := by
    have hnat : (1129807713 : ℕ)^1063*100000000000000^807 ≤ 35127125861317^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129807713 2500000000 35127125861317 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208370567/500000000 : ℝ)^1063 ≤ (6314060583373/20000000000000 : ℝ)^807 := by
    have hnat : (208370567 : ℕ)^1063*20000000000000^807 ≤ 6314060583373^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208370567 500000000 6314060583373 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339886949/10000000000 : ℝ), (1129807713/2500000000 : ℝ), (208370567/500000000 : ℝ)] ![(33302571208933/100000000000000 : ℝ), (35127125861317/100000000000000 : ℝ), (6314060583373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339886949/10000000000 : ℝ)|^1063 ≤ (33302571208933/100000000000000 : ℝ)^807
        have hw : |(4339886949/10000000000 : ℝ)|=(4339886949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129807713/2500000000 : ℝ)|^1063 ≤ (35127125861317/100000000000000 : ℝ)^807
        have hw : |(1129807713/2500000000 : ℝ)|=(1129807713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208370567/500000000 : ℝ)|^1063 ≤ (6314060583373/20000000000000 : ℝ)^807
        have hw : |(208370567/500000000 : ℝ)|=(208370567/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (587/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5507/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5507/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5507/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5507/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5507/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5507/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5507/50000 : ℝ) ^ (4251/1024 : ℝ) ≤ (2107619481901041/20000000000000000000 : ℝ) := by
    have hpowers : (5507/50000 : ℝ)^4251 ≤ (2107619481901041/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5507 : ℕ)^4251*20000000000000000000^1024 ≤ 2107619481901041^1024*50000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5507 50000 2107619481901041 20000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5507/50000 : ℝ)) (X := (2107619481901041/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (4251/1024 : ℝ) ≤ (34794501999183731/100000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^4251 ≤ (34794501999183731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7343 : ℕ)^4251*100000000000000000000^1024 ≤ 34794501999183731^1024*50000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 34794501999183731 100000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (34794501999183731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002107619481901041/10000000000000000000 : ℝ) ≤ (10000507652251831/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (10002107619481901041/10000000000000000000 : ℝ)^1024 ≤ (10000507652251831/10000000000000000 : ℝ)^4251 := by
      have hnat : (10002107619481901041 : ℕ)^1024*10000000000000000^4251 ≤ 10000507652251831^4251*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002107619481901041 10000000000000000000 10000507652251831 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000507652251831/10000000000000000 : ℝ)) (X := (10002107619481901041/10000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505666574926086117/12500000000000000000 : ℝ) ≤ (10001091804202167/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (12505666574926086117/12500000000000000000 : ℝ)^1024 ≤ (10001091804202167/10000000000000000 : ℝ)^4251 := by
      have hnat : (12505666574926086117 : ℕ)^1024*10000000000000000^4251 ≤ 10001091804202167^4251*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505666574926086117 12500000000000000000 10001091804202167 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001091804202167/10000000000000000 : ℝ)) (X := (12505666574926086117/12500000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034794501999183731/50000000000000000000 : ℝ) ≤ (10001675956152503/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50034794501999183731/50000000000000000000 : ℝ)^1024 ≤ (10001675956152503/10000000000000000 : ℝ)^4251 := by
      have hnat : (50034794501999183731 : ℕ)^1024*10000000000000000^4251 ≤ 10001675956152503^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034794501999183731 50000000000000000000 10001675956152503 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001675956152503/10000000000000000 : ℝ)) (X := (50034794501999183731/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2107619481901041/20000000000000000000 : ℝ) ≤ ((4588624549988340253/4590000000000000000 : ℝ)+2*(570460889/358593750000 : ℝ)*(5507/50000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (4588624549988340253/4590000000000000000 : ℝ)+2*(570460889/358593750000 : ℝ)*(5507/50000 : ℝ)=(10000507652251831/10000000000000000 : ℝ) by norm_num, show 1+2*(2107619481901041/20000000000000000000 : ℝ)=(10002107619481901041/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34794501999183731/100000000000000000000 : ℝ)+(2107619481901041/20000000000000000000 : ℝ) ≤ ((4588624549988340253/4590000000000000000 : ℝ)+(570460889/358593750000 : ℝ)*((7343/50000 : ℝ)+(5507/50000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (4588624549988340253/4590000000000000000 : ℝ)+(570460889/358593750000 : ℝ)*((7343/50000 : ℝ)+(5507/50000 : ℝ))=(10001091804202167/10000000000000000 : ℝ) by norm_num, show 1+(34794501999183731/100000000000000000000 : ℝ)+(2107619481901041/20000000000000000000 : ℝ)=(12505666574926086117/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34794501999183731/100000000000000000000 : ℝ) ≤ ((4588624549988340253/4590000000000000000 : ℝ)+2*(570460889/358593750000 : ℝ)*(7343/50000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (4588624549988340253/4590000000000000000 : ℝ)+2*(570460889/358593750000 : ℝ)*(7343/50000 : ℝ)=(10001675956152503/10000000000000000 : ℝ) by norm_num, show 1+2*(34794501999183731/100000000000000000000 : ℝ)=(50034794501999183731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4588624549988340253/4590000000000000000 : ℝ)*(X 1 0+X 2 0)+(570460889/358593750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5507/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4588624549988340253/4590000000000000000 : ℝ)) (alpha := (570460889/358593750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4588624549988340253/4590000000000000000 : ℝ)*(X 0 1+X 2 1)+(570460889/358593750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5507/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4588624549988340253/4590000000000000000 : ℝ)) (alpha := (570460889/358593750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4588624549988340253/4590000000000000000 : ℝ)*(X 0 2+X 1 2)+(570460889/358593750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5507/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (4588624549988340253/4590000000000000000 : ℝ)) (alpha := (570460889/358593750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2087962027/10000000000 : ℝ)*X 0 0+(84614393/156250000 : ℝ)*X 0 1+(20971623/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337451639/2500000000 : ℝ)*X 1 0+(-1087925891/5000000000 : ℝ)*X 1 1+(1310726443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534980651/1000000000 : ℝ)*X 2 0+(81920403/156250000 : ℝ)*X 2 1+(-1087925909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169930359/5000000000 : ℝ)*X 0 0+(266633/640000 : ℝ)*X 0 1+(4520495093/10000000000 : ℝ)*X 0 2+(2169930359/5000000000 : ℝ)*X 1 0+(266633/640000 : ℝ)*X 1 1+(4520495093/10000000000 : ℝ)*X 1 2+(2169930359/5000000000 : ℝ)*X 2 0+(266633/640000 : ℝ)*X 2 1+(4520495093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-521993699/2500000000 : ℝ)*X 0 0+(5243520827/10000000000 : ℝ)*X 0 1+(338418931/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305663803/10000000000 : ℝ)*X 1 0+(-2004054753/10000000000 : ℝ)*X 1 1+(338418927/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305663833/10000000000 : ℝ)*X 2 0+(5414702769/10000000000 : ℝ)*X 2 1+(-5010137/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339886949/10000000000 : ℝ)*X 0 0+(1129807713/2500000000 : ℝ)*X 0 1+(208370567/500000000 : ℝ)*X 0 2+(4339886949/10000000000 : ℝ)*X 1 0+(1129807713/2500000000 : ℝ)*X 1 1+(208370567/500000000 : ℝ)*X 1 2+(4339886949/10000000000 : ℝ)*X 2 0+(1129807713/2500000000 : ℝ)*X 2 1+(208370567/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172813154890895908803118891/76500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31190033/6250000000000 : ℝ)*(base19) + (54532857/12500000000000 : ℝ)*(base23) + (6904991/100000000000000 : ℝ)*(lower2) + (8481407/10000000000000 : ℝ)*(upper3) + (23812531/100000000000000 : ℝ)*(upper5) + (4311005284686349/100000000000000 : ℝ)*(major0) + (4311005284686349/100000000000000 : ℝ)*(major1) + (4311005284686349/100000000000000 : ℝ)*(major2) + (181248684734871/3125000000000 : ℝ)*(sp0) + (2899983518428779/50000000000000 : ℝ)*(sp1) + (579996709963523/10000000000000 : ℝ)*(sp2) + (141101879154937/5000000000000 : ℝ)*(sp3) + (4812191107/50000000000000 : ℝ)*(sp4) + (335942251/6250000000000 : ℝ)*(sp7) + (705510739543689/25000000000000 : ℝ)*(f.failure) + (2899983767949043/50000000000000 : ℝ)*(f.sum) + (101898678959/71718750000000000000000000 : ℝ)*base65 + (2396349168448893703/459000000000000000000000000000000 : ℝ)*base68 + (3644464883098893703/459000000000000000000000000000000 : ℝ)*base70 + (1528062126430893703/459000000000000000000000000000000 : ℝ)*base72 + (180923555657/143437500000000000000000000 : ℝ)*base74 + (5800970368786893703/459000000000000000000000000000000 : ℝ)*base76 + (3663695973298893703/459000000000000000000000000000000 : ℝ)*base78 + (5293353665290893703/459000000000000000000000000000000 : ℝ)*base80 + (1456064768749/286875000000000000000000000 : ℝ)*base82 + (18357851/2500000000000000000000 : ℝ)*base89 + (18357851/2500000000000000000000 : ℝ)*base91 + (18357851/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (906222449288996961643/85000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2006931693/100000000000000 : ℝ)*(base19) + (537391707/25000000000000 : ℝ)*(base23) + (51388507/25000000000000 : ℝ)*(upper3) + (61817277/100000000000000 : ℝ)*(lower4) + (132927737/50000000000000 : ℝ)*(upper5) + (1085512494221457/25000000000000 : ℝ)*(major0) + (1085512494221457/25000000000000 : ℝ)*(major1) + (1085512494221457/25000000000000 : ℝ)*(major2) + (39424230647/100000000000000 : ℝ)*(sp1) + (1929701053/5000000000000 : ℝ)*(sp2) + (1168346872111149/20000000000000 : ℝ)*(sp4) + (1168338585878681/20000000000000 : ℝ)*(sp5) + (5841693616967857/100000000000000 : ℝ)*(sp6) + (710591309458637/25000000000000 : ℝ)*(sp7) + (710591309458637/25000000000000 : ℝ)*(f.failure) + (1168346872111149/20000000000000 : ℝ)*(f.sum) + (408667373389/95625000000000000000000000 : ℝ)*base65 + (178915387972813793/38250000000000000000000000000000 : ℝ)*base68 + (8622991567936207/38250000000000000000000000000000 : ℝ)*base69 + (110087115736186207/38250000000000000000000000000000 : ℝ)*base71 + (3828938824187/765000000000000000000000000 : ℝ)*base73 + (423230215525063793/38250000000000000000000000000000 : ℝ)*base76 + (353304501560686207/38250000000000000000000000000000 : ℝ)*base77 + (45953585226313793/38250000000000000000000000000000 : ℝ)*base80 + (790439417749/95625000000000000000000000 : ℝ)*base81 + (28273817/2500000000000000000000 : ℝ)*base90 + (28273817/2500000000000000000000 : ℝ)*base92 + (28273817/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1292_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (587/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1292_s7_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087968987/10000000000 : ℝ)*x 0 + (541521959/1000000000 : ℝ)*x 1 + (2621501581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087968987/10000000000 : ℝ)^1063 ≤ (2540703488309/20000000000000 : ℝ)^807 := by
    have hnat : (2087968987 : ℕ)^1063*20000000000000^807 ≤ 2540703488309^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087968987 10000000000 2540703488309 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541521959/1000000000 : ℝ)^1063 ≤ (22288591509349/50000000000000 : ℝ)^807 := by
    have hnat : (541521959 : ℕ)^1063*50000000000000^807 ≤ 22288591509349^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541521959 1000000000 22288591509349 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621501581/5000000000 : ℝ)^1063 ≤ (2669956220321/6250000000000 : ℝ)^807 := by
    have hnat : (2621501581 : ℕ)^1063*6250000000000^807 ≤ 2669956220321^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621501581 5000000000 2669956220321 6250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087968987/10000000000 : ℝ), (541521959/1000000000 : ℝ), (2621501581/5000000000 : ℝ)] ![(2540703488309/20000000000000 : ℝ), (22288591509349/50000000000000 : ℝ), (2669956220321/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087968987/10000000000 : ℝ)|^1063 ≤ (2540703488309/20000000000000 : ℝ)^807
        have hw : |(-2087968987/10000000000 : ℝ)|=(2087968987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541521959/1000000000 : ℝ)|^1063 ≤ (22288591509349/50000000000000 : ℝ)^807
        have hw : |(541521959/1000000000 : ℝ)|=(541521959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621501581/5000000000 : ℝ)|^1063 ≤ (2669956220321/6250000000000 : ℝ)^807
        have hw : |(2621501581/5000000000 : ℝ)|=(2621501581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069956459/2000000000 : ℝ)*x 0 + (-2175756353/10000000000 : ℝ)*x 1 + (5243002387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069956459/2000000000 : ℝ)^1063 ≤ (10967249752279/25000000000000 : ℝ)^807 := by
    have hnat : (1069956459 : ℕ)^1063*25000000000000^807 ≤ 10967249752279^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069956459 2000000000 10967249752279 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175756353/10000000000 : ℝ)^1063 ≤ (3352927445379/25000000000000 : ℝ)^807 := by
    have hnat : (2175756353 : ℕ)^1063*25000000000000^807 ≤ 3352927445379^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175756353 10000000000 3352927445379 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243002387/10000000000 : ℝ)^1063 ≤ (21359645603697/50000000000000 : ℝ)^807 := by
    have hnat : (5243002387 : ℕ)^1063*50000000000000^807 ≤ 21359645603697^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243002387 10000000000 21359645603697 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069956459/2000000000 : ℝ), (-2175756353/10000000000 : ℝ), (5243002387/10000000000 : ℝ)] ![(10967249752279/25000000000000 : ℝ), (3352927445379/25000000000000 : ℝ), (21359645603697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069956459/2000000000 : ℝ)|^1063 ≤ (10967249752279/25000000000000 : ℝ)^807
        have hw : |(1069956459/2000000000 : ℝ)|=(1069956459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175756353/10000000000 : ℝ)|^1063 ≤ (3352927445379/25000000000000 : ℝ)^807
        have hw : |(-2175756353/10000000000 : ℝ)|=(2175756353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243002387/10000000000 : ℝ)|^1063 ≤ (21359645603697/50000000000000 : ℝ)^807
        have hw : |(5243002387/10000000000 : ℝ)|=(5243002387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534978271/1000000000 : ℝ)*x 0 + (5243002157/10000000000 : ℝ)*x 1 + (-1087878051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534978271/1000000000 : ℝ)^1063 ≤ (4386900349171/10000000000000 : ℝ)^807 := by
    have hnat : (534978271 : ℕ)^1063*10000000000000^807 ≤ 4386900349171^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534978271 1000000000 4386900349171 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243002157/10000000000 : ℝ)^1063 ≤ (42719288738903/100000000000000 : ℝ)^807 := by
    have hnat : (5243002157 : ℕ)^1063*100000000000000^807 ≤ 42719288738903^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243002157 10000000000 42719288738903 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087878051/5000000000 : ℝ)^1063 ≤ (6705853871751/50000000000000 : ℝ)^807 := by
    have hnat : (1087878051 : ℕ)^1063*50000000000000^807 ≤ 6705853871751^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087878051 5000000000 6705853871751 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534978271/1000000000 : ℝ), (5243002157/10000000000 : ℝ), (-1087878051/5000000000 : ℝ)] ![(4386900349171/10000000000000 : ℝ), (42719288738903/100000000000000 : ℝ), (6705853871751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534978271/1000000000 : ℝ)|^1063 ≤ (4386900349171/10000000000000 : ℝ)^807
        have hw : |(534978271/1000000000 : ℝ)|=(534978271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243002157/10000000000 : ℝ)|^1063 ≤ (42719288738903/100000000000000 : ℝ)^807
        have hw : |(5243002157/10000000000 : ℝ)|=(5243002157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087878051/5000000000 : ℝ)|^1063 ≤ (6705853871751/50000000000000 : ℝ)^807
        have hw : |(-1087878051/5000000000 : ℝ)|=(1087878051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4339866793/10000000000 : ℝ)*x 0 + (2083172287/5000000000 : ℝ)*x 1 + (2260145179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339866793/10000000000 : ℝ)^1063 ≤ (16651183737561/50000000000000 : ℝ)^807 := by
    have hnat : (4339866793 : ℕ)^1063*50000000000000^807 ≤ 16651183737561^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339866793 10000000000 16651183737561 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083172287/5000000000 : ℝ)^1063 ≤ (7889914614177/25000000000000 : ℝ)^807 := by
    have hnat : (2083172287 : ℕ)^1063*25000000000000^807 ≤ 7889914614177^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083172287 5000000000 7889914614177 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260145179/5000000000 : ℝ)^1063 ≤ (35137974053961/100000000000000 : ℝ)^807 := by
    have hnat : (2260145179 : ℕ)^1063*100000000000000^807 ≤ 35137974053961^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260145179 5000000000 35137974053961 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339866793/10000000000 : ℝ), (2083172287/5000000000 : ℝ), (2260145179/5000000000 : ℝ)] ![(16651183737561/50000000000000 : ℝ), (7889914614177/25000000000000 : ℝ), (35137974053961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339866793/10000000000 : ℝ)|^1063 ≤ (16651183737561/50000000000000 : ℝ)^807
        have hw : |(4339866793/10000000000 : ℝ)|=(4339866793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083172287/5000000000 : ℝ)|^1063 ≤ (7889914614177/25000000000000 : ℝ)^807
        have hw : |(2083172287/5000000000 : ℝ)|=(2083172287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2260145179/5000000000 : ℝ)|^1063 ≤ (35137974053961/100000000000000 : ℝ)^807
        have hw : |(2260145179/5000000000 : ℝ)|=(2260145179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-104399097/500000000 : ℝ)*x 0 + (131090413/250000000 : ℝ)*x 1 + (5414602893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104399097/500000000 : ℝ)^1063 ≤ (12703621249459/100000000000000 : ℝ)^807 := by
    have hnat : (104399097 : ℕ)^1063*100000000000000^807 ≤ 12703621249459^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104399097 500000000 12703621249459 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131090413/250000000 : ℝ)^1063 ≤ (42725882555001/100000000000000 : ℝ)^807 := by
    have hnat : (131090413 : ℕ)^1063*100000000000000^807 ≤ 42725882555001^807*250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131090413 250000000 42725882555001 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414602893/10000000000 : ℝ)^1063 ≤ (5571312023613/12500000000000 : ℝ)^807 := by
    have hnat : (5414602893 : ℕ)^1063*12500000000000^807 ≤ 5571312023613^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414602893 10000000000 5571312023613 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104399097/500000000 : ℝ), (131090413/250000000 : ℝ), (5414602893/10000000000 : ℝ)] ![(12703621249459/100000000000000 : ℝ), (42725882555001/100000000000000 : ℝ), (5571312023613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104399097/500000000 : ℝ)|^1063 ≤ (12703621249459/100000000000000 : ℝ)^807
        have hw : |(-104399097/500000000 : ℝ)|=(104399097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131090413/250000000 : ℝ)|^1063 ≤ (42725882555001/100000000000000 : ℝ)^807
        have hw : |(131090413/250000000 : ℝ)|=(131090413/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414602893/10000000000 : ℝ)|^1063 ≤ (5571312023613/12500000000000 : ℝ)^807
        have hw : |(5414602893/10000000000 : ℝ)|=(5414602893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845063/5000000000 : ℝ)*x 0 + (-2004155889/10000000000 : ℝ)*x 1 + (1353650723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845063/5000000000 : ℝ)^1063 ≤ (1356042631211/3125000000000 : ℝ)^807 := by
    have hnat : (2652845063 : ℕ)^1063*3125000000000^807 ≤ 1356042631211^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845063 5000000000 1356042631211 3125000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004155889/10000000000 : ℝ)^1063 ≤ (1504517450601/12500000000000 : ℝ)^807 := by
    have hnat : (2004155889 : ℕ)^1063*12500000000000^807 ≤ 1504517450601^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004155889 10000000000 1504517450601 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353650723/2500000000 : ℝ)^1063 ≤ (44570496178061/100000000000000 : ℝ)^807 := by
    have hnat : (1353650723 : ℕ)^1063*100000000000000^807 ≤ 44570496178061^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353650723 2500000000 44570496178061 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845063/5000000000 : ℝ), (-2004155889/10000000000 : ℝ), (1353650723/2500000000 : ℝ)] ![(1356042631211/3125000000000 : ℝ), (1504517450601/12500000000000 : ℝ), (44570496178061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845063/5000000000 : ℝ)|^1063 ≤ (1356042631211/3125000000000 : ℝ)^807
        have hw : |(2652845063/5000000000 : ℝ)|=(2652845063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004155889/10000000000 : ℝ)|^1063 ≤ (1504517450601/12500000000000 : ℝ)^807
        have hw : |(-2004155889/10000000000 : ℝ)|=(2004155889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353650723/2500000000 : ℝ)|^1063 ≤ (44570496178061/100000000000000 : ℝ)^807
        have hw : |(1353650723/2500000000 : ℝ)|=(1353650723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845063/5000000000 : ℝ)*x 0 + (5414602893/10000000000 : ℝ)*x 1 + (-125259743/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845063/5000000000 : ℝ)^1063 ≤ (1356042631211/3125000000000 : ℝ)^807 := by
    have hnat : (2652845063 : ℕ)^1063*3125000000000^807 ≤ 1356042631211^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845063 5000000000 1356042631211 3125000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414602893/10000000000 : ℝ)^1063 ≤ (5571312023613/12500000000000 : ℝ)^807 := by
    have hnat : (5414602893 : ℕ)^1063*12500000000000^807 ≤ 5571312023613^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414602893 10000000000 5571312023613 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125259743/625000000 : ℝ)^1063 ≤ (12036139596897/100000000000000 : ℝ)^807 := by
    have hnat : (125259743 : ℕ)^1063*100000000000000^807 ≤ 12036139596897^807*625000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125259743 625000000 12036139596897 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845063/5000000000 : ℝ), (5414602893/10000000000 : ℝ), (-125259743/625000000 : ℝ)] ![(1356042631211/3125000000000 : ℝ), (5571312023613/12500000000000 : ℝ), (12036139596897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845063/5000000000 : ℝ)|^1063 ≤ (1356042631211/3125000000000 : ℝ)^807
        have hw : |(2652845063/5000000000 : ℝ)|=(2652845063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414602893/10000000000 : ℝ)|^1063 ≤ (5571312023613/12500000000000 : ℝ)^807
        have hw : |(5414602893/10000000000 : ℝ)|=(5414602893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125259743/625000000 : ℝ)|^1063 ≤ (12036139596897/100000000000000 : ℝ)^807
        have hw : |(-125259743/625000000 : ℝ)|=(125259743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s7_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1084973467/2500000000 : ℝ)*x 0 + (4519028999/10000000000 : ℝ)*x 1 + (2083805719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084973467/2500000000 : ℝ)^1063 ≤ (8325660286303/25000000000000 : ℝ)^807 := by
    have hnat : (1084973467 : ℕ)^1063*25000000000000^807 ≤ 8325660286303^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084973467 2500000000 8325660286303 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519028999/10000000000 : ℝ)^1063 ≤ (702501183939/2000000000000 : ℝ)^807 := by
    have hnat : (4519028999 : ℕ)^1063*2000000000000^807 ≤ 702501183939^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519028999 10000000000 702501183939 2000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083805719/5000000000 : ℝ)^1063 ≤ (3946537455181/12500000000000 : ℝ)^807 := by
    have hnat : (2083805719 : ℕ)^1063*12500000000000^807 ≤ 3946537455181^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083805719 5000000000 3946537455181 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084973467/2500000000 : ℝ), (4519028999/10000000000 : ℝ), (2083805719/5000000000 : ℝ)] ![(8325660286303/25000000000000 : ℝ), (702501183939/2000000000000 : ℝ), (3946537455181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084973467/2500000000 : ℝ)|^1063 ≤ (8325660286303/25000000000000 : ℝ)^807
        have hw : |(1084973467/2500000000 : ℝ)|=(1084973467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519028999/10000000000 : ℝ)|^1063 ≤ (702501183939/2000000000000 : ℝ)^807
        have hw : |(4519028999/10000000000 : ℝ)|=(4519028999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083805719/5000000000 : ℝ)|^1063 ≤ (3946537455181/12500000000000 : ℝ)^807
        have hw : |(2083805719/5000000000 : ℝ)|=(2083805719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2757/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (917/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5513/50000 : ℝ) ^ (4251/1024 : ℝ) ≤ (10585843195290883/100000000000000000000 : ℝ) := by
    have hpowers : (5513/50000 : ℝ)^4251 ≤ (10585843195290883/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5513 : ℕ)^4251*100000000000000000000^1024 ≤ 10585843195290883^1024*50000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5513 50000 10585843195290883 100000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5513/50000 : ℝ)) (X := (10585843195290883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (587/4000 : ℝ) ^ (4251/1024 : ℝ) ≤ (34686438668240979/100000000000000000000 : ℝ) := by
    have hpowers : (587/4000 : ℝ)^4251 ≤ (34686438668240979/100000000000000000000 : ℝ)^1024 := by
      have hnat : (587 : ℕ)^4251*100000000000000000000^1024 ≤ 34686438668240979^1024*4000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        587 4000 34686438668240979 100000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (587/4000 : ℝ)) (X := (34686438668240979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010585843195290883/50000000000000000000 : ℝ) ≤ (10000509952126969/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50010585843195290883/50000000000000000000 : ℝ)^1024 ≤ (10000509952126969/10000000000000000 : ℝ)^4251 := by
      have hnat : (50010585843195290883 : ℕ)^1024*10000000000000000^4251 ≤ 10000509952126969^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010585843195290883 50000000000000000000 10000509952126969 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000509952126969/10000000000000000 : ℝ)) (X := (50010585843195290883/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022636140931765931/50000000000000000000 : ℝ) ≤ (10001090351745479/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50022636140931765931/50000000000000000000 : ℝ)^1024 ≤ (10001090351745479/10000000000000000 : ℝ)^4251 := by
      have hnat : (50022636140931765931 : ℕ)^1024*10000000000000000^4251 ≤ 10001090351745479^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022636140931765931 50000000000000000000 10001090351745479 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001090351745479/10000000000000000 : ℝ)) (X := (50022636140931765931/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034686438668240979/50000000000000000000 : ℝ) ≤ (10001670751363989/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50034686438668240979/50000000000000000000 : ℝ)^1024 ≤ (10001670751363989/10000000000000000 : ℝ)^4251 := by
      have hnat : (50034686438668240979 : ℕ)^1024*10000000000000000^4251 ≤ 10001670751363989^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034686438668240979 50000000000000000000 10001670751363989 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001670751363989/10000000000000000 : ℝ)) (X := (50034686438668240979/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10585843195290883/100000000000000000000 : ℝ) ≤ ((36479061842923927361/36490000000000000000 : ℝ)+2*(58039961851/36490000000000 : ℝ)*(5513/50000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (36479061842923927361/36490000000000000000 : ℝ)+2*(58039961851/36490000000000 : ℝ)*(5513/50000 : ℝ)=(10000509952126969/10000000000000000 : ℝ) by norm_num, show 1+2*(10585843195290883/100000000000000000000 : ℝ)=(50010585843195290883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34686438668240979/100000000000000000000 : ℝ)+(10585843195290883/100000000000000000000 : ℝ) ≤ ((36479061842923927361/36490000000000000000 : ℝ)+(58039961851/36490000000000 : ℝ)*((587/4000 : ℝ)+(5513/50000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (36479061842923927361/36490000000000000000 : ℝ)+(58039961851/36490000000000 : ℝ)*((587/4000 : ℝ)+(5513/50000 : ℝ))=(10001090351745479/10000000000000000 : ℝ) by norm_num, show 1+(34686438668240979/100000000000000000000 : ℝ)+(10585843195290883/100000000000000000000 : ℝ)=(50022636140931765931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34686438668240979/100000000000000000000 : ℝ) ≤ ((36479061842923927361/36490000000000000000 : ℝ)+2*(58039961851/36490000000000 : ℝ)*(587/4000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (36479061842923927361/36490000000000000000 : ℝ)+2*(58039961851/36490000000000 : ℝ)*(587/4000 : ℝ)=(10001670751363989/10000000000000000 : ℝ) by norm_num, show 1+2*(34686438668240979/100000000000000000000 : ℝ)=(50034686438668240979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36479061842923927361/36490000000000000000 : ℝ)*(X 1 0+X 2 0)+(58039961851/36490000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (36479061842923927361/36490000000000000000 : ℝ)) (alpha := (58039961851/36490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36479061842923927361/36490000000000000000 : ℝ)*(X 0 1+X 2 1)+(58039961851/36490000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (36479061842923927361/36490000000000000000 : ℝ)) (alpha := (58039961851/36490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36479061842923927361/36490000000000000000 : ℝ)*(X 0 2+X 1 2)+(58039961851/36490000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (36479061842923927361/36490000000000000000 : ℝ)) (alpha := (58039961851/36490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2087968987/10000000000 : ℝ)*X 0 0+(541521959/1000000000 : ℝ)*X 0 1+(2621501581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069956459/2000000000 : ℝ)*X 1 0+(-2175756353/10000000000 : ℝ)*X 1 1+(5243002387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534978271/1000000000 : ℝ)*X 2 0+(5243002157/10000000000 : ℝ)*X 2 1+(-1087878051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339866793/10000000000 : ℝ)*X 0 0+(2083172287/5000000000 : ℝ)*X 0 1+(2260145179/5000000000 : ℝ)*X 0 2+(4339866793/10000000000 : ℝ)*X 1 0+(2083172287/5000000000 : ℝ)*X 1 1+(2260145179/5000000000 : ℝ)*X 1 2+(4339866793/10000000000 : ℝ)*X 2 0+(2083172287/5000000000 : ℝ)*X 2 1+(2260145179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104399097/500000000 : ℝ)*X 0 0+(131090413/250000000 : ℝ)*X 0 1+(5414602893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652845063/5000000000 : ℝ)*X 1 0+(-2004155889/10000000000 : ℝ)*X 1 1+(1353650723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652845063/5000000000 : ℝ)*X 2 0+(5414602893/10000000000 : ℝ)*X 2 1+(-125259743/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1084973467/2500000000 : ℝ)*X 0 0+(4519028999/10000000000 : ℝ)*X 0 1+(2083805719/5000000000 : ℝ)*X 0 2+(1084973467/2500000000 : ℝ)*X 1 0+(4519028999/10000000000 : ℝ)*X 1 1+(2083805719/5000000000 : ℝ)*X 1 2+(1084973467/2500000000 : ℝ)*X 2 0+(4519028999/10000000000 : ℝ)*X 2 1+(2083805719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1601293482698976430033999977/456125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239043893/100000000000000 : ℝ)*(base19) + (555628083/100000000000000 : ℝ)*(base23) + (78420761/50000000000000 : ℝ)*(lower3) + (99358017/100000000000000 : ℝ)*(upper4) + (30705161/25000000000000 : ℝ)*(lower5) + (2157982309421181/50000000000000 : ℝ)*(major0) + (2157982309421181/50000000000000 : ℝ)*(major1) + (2157982309421181/50000000000000 : ℝ)*(major2) + (5806639714593327/100000000000000 : ℝ)*(sp0) + (2903314508771059/50000000000000 : ℝ)*(sp1) + (5806634994209911/100000000000000 : ℝ)*(sp2) + (56505788121397/2000000000000 : ℝ)*(sp3) + (2614501829/25000000000000 : ℝ)*(sp5) + (1041188833/25000000000000 : ℝ)*(sp6) + (56505788121397/2000000000000 : ℝ)*(f.failure) + (5806639714593327/100000000000000 : ℝ)*(f.sum) + (1081846397729/145960000000000000000000000 : ℝ)*base66 + (7693196710394833341/1824500000000000000000000000000000 : ℝ)*base67 + (16563666768316833341/1824500000000000000000000000000000 : ℝ)*base69 + (7742591166632166659/1824500000000000000000000000000000 : ℝ)*base72 + (3309698688427/1824500000000000000000000000 : ℝ)*base74 + (5046157360798833341/1824500000000000000000000000000000 : ℝ)*base75 + (23736368468175833341/1824500000000000000000000000000000 : ℝ)*base77 + (22445232378456333341/1824500000000000000000000000000000 : ℝ)*base79 + (2274751501307/1824500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (602977/200000000000000000000 : ℝ)*base90 + (602977/200000000000000000000 : ℝ)*base92 + (602977/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4359148838336706849596686509/1824500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (404647441/100000000000000 : ℝ)*(base19) + (112952809/25000000000000 : ℝ)*(base23) + (5539411/4000000000000 : ℝ)*(lower1) + (11619201/25000000000000 : ℝ)*(upper3) + (4199769/20000000000000 : ℝ)*(lower4) + (11210629/25000000000000 : ℝ)*(upper5) + (4347012167345777/100000000000000 : ℝ)*(major0) + (4347012167345777/100000000000000 : ℝ)*(major1) + (4347012167345777/100000000000000 : ℝ)*(major2) + (912807461/100000000000000 : ℝ)*(sp2) + (116968213990907/2000000000000 : ℝ)*(sp4) + (5848410294897909/100000000000000 : ℝ)*(sp5) + (1462102333731663/25000000000000 : ℝ)*(sp6) + (355701694438153/12500000000000 : ℝ)*(sp7) + (355701694438153/12500000000000 : ℝ)*(f.failure) + (116968213990907/2000000000000 : ℝ)*(f.sum) + (219031816457/1824500000000000000000000000 : ℝ)*base66 + (12200991598278895503/3649000000000000000000000000000000 : ℝ)*base68 + (15744229444707104497/3649000000000000000000000000000000 : ℝ)*base69 + (23476229448411104497/3649000000000000000000000000000000 : ℝ)*base71 + (829481802621/3649000000000000000000000000 : ℝ)*base74 + (2579060864714895503/3649000000000000000000000000000000 : ℝ)*base76 + (12864605652139104497/3649000000000000000000000000000000 : ℝ)*base77 + (27713537929884104497/3649000000000000000000000000000000 : ℝ)*base79 + (352868340383/912250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (306427/1250000000000000000000 : ℝ)*base89 + (306427/1250000000000000000000 : ℝ)*base91 + (306427/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1292_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (917/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1292_box_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-383325699/2000000000 : ℝ)*x 0 + (5392011917/10000000000 : ℝ)*x 1 + (2696005973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383325699/2000000000 : ℝ)^1063 ≤ (2269716138777/20000000000000 : ℝ)^807 := by
    have hnat : (383325699 : ℕ)^1063*20000000000000^807 ≤ 2269716138777^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383325699 2000000000 2269716138777 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392011917/10000000000 : ℝ)^1063 ≤ (2770356843263/6250000000000 : ℝ)^807 := by
    have hnat : (5392011917 : ℕ)^1063*6250000000000^807 ≤ 2770356843263^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392011917 10000000000 2770356843263 6250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696005973/5000000000 : ℝ)^1063 ≤ (5540713725779/12500000000000 : ℝ)^807 := by
    have hnat : (2696005973 : ℕ)^1063*12500000000000^807 ≤ 5540713725779^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696005973 5000000000 5540713725779 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383325699/2000000000 : ℝ), (5392011917/10000000000 : ℝ), (2696005973/5000000000 : ℝ)] ![(2269716138777/20000000000000 : ℝ), (2770356843263/6250000000000 : ℝ), (5540713725779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383325699/2000000000 : ℝ)|^1063 ≤ (2269716138777/20000000000000 : ℝ)^807
        have hw : |(-383325699/2000000000 : ℝ)|=(383325699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392011917/10000000000 : ℝ)|^1063 ≤ (2770356843263/6250000000000 : ℝ)^807
        have hw : |(5392011917/10000000000 : ℝ)|=(5392011917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696005973/5000000000 : ℝ)|^1063 ≤ (5540713725779/12500000000000 : ℝ)^807
        have hw : |(2696005973/5000000000 : ℝ)|=(2696005973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5284369111/10000000000 : ℝ)*x 0 + (-2063836569/10000000000 : ℝ)*x 1 + (5392012131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284369111/10000000000 : ℝ)^1063 ≤ (2697738566047/6250000000000 : ℝ)^807 := by
    have hnat : (5284369111 : ℕ)^1063*6250000000000^807 ≤ 2697738566047^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284369111 10000000000 2697738566047 6250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063836569/10000000000 : ℝ)^1063 ≤ (195476111327/1562500000000 : ℝ)^807 := by
    have hnat : (2063836569 : ℕ)^1063*1562500000000^807 ≤ 195476111327^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063836569 10000000000 195476111327 1562500000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392012131/10000000000 : ℝ)^1063 ≤ (44325711809487/100000000000000 : ℝ)^807 := by
    have hnat : (5392012131 : ℕ)^1063*100000000000000^807 ≤ 44325711809487^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392012131 10000000000 44325711809487 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284369111/10000000000 : ℝ), (-2063836569/10000000000 : ℝ), (5392012131/10000000000 : ℝ)] ![(2697738566047/6250000000000 : ℝ), (195476111327/1562500000000 : ℝ), (44325711809487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284369111/10000000000 : ℝ)|^1063 ≤ (2697738566047/6250000000000 : ℝ)^807
        have hw : |(5284369111/10000000000 : ℝ)|=(5284369111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063836569/10000000000 : ℝ)|^1063 ≤ (195476111327/1562500000000 : ℝ)^807
        have hw : |(-2063836569/10000000000 : ℝ)|=(2063836569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392012131/10000000000 : ℝ)|^1063 ≤ (44325711809487/100000000000000 : ℝ)^807
        have hw : |(5392012131/10000000000 : ℝ)|=(5392012131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5284369521/10000000000 : ℝ)*x 0 + (674001471/1250000000 : ℝ)*x 1 + (-2063836509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284369521/10000000000 : ℝ)^1063 ≤ (4316382146809/10000000000000 : ℝ)^807 := by
    have hnat : (5284369521 : ℕ)^1063*10000000000000^807 ≤ 4316382146809^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284369521 10000000000 4316382146809 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674001471/1250000000 : ℝ)^1063 ≤ (1773028315151/4000000000000 : ℝ)^807 := by
    have hnat : (674001471 : ℕ)^1063*4000000000000^807 ≤ 1773028315151^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674001471 1250000000 1773028315151 4000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063836509/10000000000 : ℝ)^1063 ≤ (6255235322923/50000000000000 : ℝ)^807 := by
    have hnat : (2063836509 : ℕ)^1063*50000000000000^807 ≤ 6255235322923^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063836509 10000000000 6255235322923 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284369521/10000000000 : ℝ), (674001471/1250000000 : ℝ), (-2063836509/10000000000 : ℝ)] ![(4316382146809/10000000000000 : ℝ), (1773028315151/4000000000000 : ℝ), (6255235322923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284369521/10000000000 : ℝ)|^1063 ≤ (4316382146809/10000000000000 : ℝ)^807
        have hw : |(5284369521/10000000000 : ℝ)|=(5284369521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674001471/1250000000 : ℝ)|^1063 ≤ (1773028315151/4000000000000 : ℝ)^807
        have hw : |(674001471/1250000000 : ℝ)|=(674001471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063836509/10000000000 : ℝ)|^1063 ≤ (6255235322923/50000000000000 : ℝ)^807
        have hw : |(-2063836509/10000000000 : ℝ)|=(2063836509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4489291447/10000000000 : ℝ)*x 0 + (4269161453/10000000000 : ℝ)*x 1 + (4269161613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489291447/10000000000 : ℝ)^1063 ≤ (34820912805771/100000000000000 : ℝ)^807 := by
    have hnat : (4489291447 : ℕ)^1063*100000000000000^807 ≤ 34820912805771^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489291447 10000000000 34820912805771 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4269161453/10000000000 : ℝ)^1063 ≤ (16294771393683/50000000000000 : ℝ)^807 := by
    have hnat : (4269161453 : ℕ)^1063*50000000000000^807 ≤ 16294771393683^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269161453 10000000000 16294771393683 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4269161613/10000000000 : ℝ)^1063 ≤ (4073693049527/12500000000000 : ℝ)^807 := by
    have hnat : (4269161613 : ℕ)^1063*12500000000000^807 ≤ 4073693049527^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269161613 10000000000 4073693049527 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489291447/10000000000 : ℝ), (4269161453/10000000000 : ℝ), (4269161613/10000000000 : ℝ)] ![(34820912805771/100000000000000 : ℝ), (16294771393683/50000000000000 : ℝ), (4073693049527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489291447/10000000000 : ℝ)|^1063 ≤ (34820912805771/100000000000000 : ℝ)^807
        have hw : |(4489291447/10000000000 : ℝ)|=(4489291447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4269161453/10000000000 : ℝ)|^1063 ≤ (16294771393683/50000000000000 : ℝ)^807
        have hw : |(4269161453/10000000000 : ℝ)|=(4269161453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4269161613/10000000000 : ℝ)|^1063 ≤ (4073693049527/12500000000000 : ℝ)^807
        have hw : |(4269161613/10000000000 : ℝ)|=(4269161613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2262077459/10000000000 : ℝ)*x 0 + (657961831/1250000000 : ℝ)*x 1 + (5263695127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2262077459/10000000000 : ℝ)^1063 ≤ (3529243094157/25000000000000 : ℝ)^807 := by
    have hnat : (2262077459 : ℕ)^1063*25000000000000^807 ≤ 3529243094157^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262077459 10000000000 3529243094157 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657961831/1250000000 : ℝ)^1063 ≤ (42941511233249/100000000000000 : ℝ)^807 := by
    have hnat : (657961831 : ℕ)^1063*100000000000000^807 ≤ 42941511233249^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657961831 1250000000 42941511233249 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263695127/10000000000 : ℝ)^1063 ≤ (42941516380577/100000000000000 : ℝ)^807 := by
    have hnat : (5263695127 : ℕ)^1063*100000000000000^807 ≤ 42941516380577^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263695127 10000000000 42941516380577 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2262077459/10000000000 : ℝ), (657961831/1250000000 : ℝ), (5263695127/10000000000 : ℝ)] ![(3529243094157/25000000000000 : ℝ), (42941511233249/100000000000000 : ℝ), (42941516380577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2262077459/10000000000 : ℝ)|^1063 ≤ (3529243094157/25000000000000 : ℝ)^807
        have hw : |(-2262077459/10000000000 : ℝ)|=(2262077459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657961831/1250000000 : ℝ)|^1063 ≤ (42941511233249/100000000000000 : ℝ)^807
        have hw : |(657961831/1250000000 : ℝ)|=(657961831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263695127/10000000000 : ℝ)|^1063 ≤ (42941516380577/100000000000000 : ℝ)^807
        have hw : |(5263695127/10000000000 : ℝ)|=(5263695127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2687344863/5000000000 : ℝ)*x 0 + (-2114957851/10000000000 : ℝ)*x 1 + (5263694821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687344863/5000000000 : ℝ)^1063 ≤ (8827646680113/20000000000000 : ℝ)^807 := by
    have hnat : (2687344863 : ℕ)^1063*20000000000000^807 ≤ 8827646680113^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687344863 5000000000 8827646680113 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114957851/10000000000 : ℝ)^1063 ≤ (6460126747203/50000000000000 : ℝ)^807 := by
    have hnat : (2114957851 : ℕ)^1063*50000000000000^807 ≤ 6460126747203^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114957851 10000000000 6460126747203 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263694821/10000000000 : ℝ)^1063 ≤ (8588302618461/20000000000000 : ℝ)^807 := by
    have hnat : (5263694821 : ℕ)^1063*20000000000000^807 ≤ 8588302618461^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263694821 10000000000 8588302618461 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687344863/5000000000 : ℝ), (-2114957851/10000000000 : ℝ), (5263694821/10000000000 : ℝ)] ![(8827646680113/20000000000000 : ℝ), (6460126747203/50000000000000 : ℝ), (8588302618461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687344863/5000000000 : ℝ)|^1063 ≤ (8827646680113/20000000000000 : ℝ)^807
        have hw : |(2687344863/5000000000 : ℝ)|=(2687344863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114957851/10000000000 : ℝ)|^1063 ≤ (6460126747203/50000000000000 : ℝ)^807
        have hw : |(-2114957851/10000000000 : ℝ)|=(2114957851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263694821/10000000000 : ℝ)|^1063 ≤ (8588302618461/20000000000000 : ℝ)^807
        have hw : |(5263694821/10000000000 : ℝ)|=(5263694821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5374689513/10000000000 : ℝ)*x 0 + (5263695003/10000000000 : ℝ)*x 1 + (-1057478947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374689513/10000000000 : ℝ)^1063 ≤ (11034557774117/25000000000000 : ℝ)^807 := by
    have hnat : (5374689513 : ℕ)^1063*25000000000000^807 ≤ 11034557774117^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374689513 10000000000 11034557774117 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263695003/10000000000 : ℝ)^1063 ≤ (1717660601923/4000000000000 : ℝ)^807 := by
    have hnat : (5263695003 : ℕ)^1063*4000000000000^807 ≤ 1717660601923^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263695003 10000000000 1717660601923 4000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057478947/5000000000 : ℝ)^1063 ≤ (12920253840423/100000000000000 : ℝ)^807 := by
    have hnat : (1057478947 : ℕ)^1063*100000000000000^807 ≤ 12920253840423^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057478947 5000000000 12920253840423 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374689513/10000000000 : ℝ), (5263695003/10000000000 : ℝ), (-1057478947/5000000000 : ℝ)] ![(11034557774117/25000000000000 : ℝ), (1717660601923/4000000000000 : ℝ), (12920253840423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374689513/10000000000 : ℝ)|^1063 ≤ (11034557774117/25000000000000 : ℝ)^807
        have hw : |(5374689513/10000000000 : ℝ)|=(5374689513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263695003/10000000000 : ℝ)|^1063 ≤ (1717660601923/4000000000000 : ℝ)^807
        have hw : |(5263695003/10000000000 : ℝ)|=(5263695003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057478947/5000000000 : ℝ)|^1063 ≤ (12920253840423/100000000000000 : ℝ)^807
        have hw : |(-1057478947/5000000000 : ℝ)|=(1057478947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2094797199/5000000000 : ℝ)*x 0 + (276184669/625000000 : ℝ)*x 1 + (1104738671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094797199/5000000000 : ℝ)^1063 ≤ (15895923357543/50000000000000 : ℝ)^807 := by
    have hnat : (2094797199 : ℕ)^1063*50000000000000^807 ≤ 15895923357543^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094797199 5000000000 15895923357543 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276184669/625000000 : ℝ)^1063 ≤ (34104076736309/100000000000000 : ℝ)^807 := by
    have hnat : (276184669 : ℕ)^1063*100000000000000^807 ≤ 34104076736309^807*625000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276184669 625000000 34104076736309 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104738671/2500000000 : ℝ)^1063 ≤ (34104076532991/100000000000000 : ℝ)^807 := by
    have hnat : (1104738671 : ℕ)^1063*100000000000000^807 ≤ 34104076532991^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104738671 2500000000 34104076532991 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094797199/5000000000 : ℝ), (276184669/625000000 : ℝ), (1104738671/2500000000 : ℝ)] ![(15895923357543/50000000000000 : ℝ), (34104076736309/100000000000000 : ℝ), (34104076532991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094797199/5000000000 : ℝ)|^1063 ≤ (15895923357543/50000000000000 : ℝ)^807
        have hw : |(2094797199/5000000000 : ℝ)|=(2094797199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(276184669/625000000 : ℝ)|^1063 ≤ (34104076736309/100000000000000 : ℝ)^807
        have hw : |(276184669/625000000 : ℝ)|=(276184669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104738671/2500000000 : ℝ)|^1063 ≤ (34104076532991/100000000000000 : ℝ)^807
        have hw : |(1104738671/2500000000 : ℝ)|=(1104738671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_8 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094837473/5000000000 : ℝ)*x 0 + (5175601113/10000000000 : ℝ)*x 1 + (5406049867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094837473/5000000000 : ℝ)^1063 ≤ (13524837427919/100000000000000 : ℝ)^807 := by
    have hnat : (1094837473 : ℕ)^1063*100000000000000^807 ≤ 13524837427919^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094837473 5000000000 13524837427919 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175601113/10000000000 : ℝ)^1063 ≤ (41997381698109/100000000000000 : ℝ)^807 := by
    have hnat : (5175601113 : ℕ)^1063*100000000000000^807 ≤ 41997381698109^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175601113 10000000000 41997381698109 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406049867/10000000000 : ℝ)^1063 ≤ (8895556173167/20000000000000 : ℝ)^807 := by
    have hnat : (5406049867 : ℕ)^1063*20000000000000^807 ≤ 8895556173167^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406049867 10000000000 8895556173167 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094837473/5000000000 : ℝ), (5175601113/10000000000 : ℝ), (5406049867/10000000000 : ℝ)] ![(13524837427919/100000000000000 : ℝ), (41997381698109/100000000000000 : ℝ), (8895556173167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094837473/5000000000 : ℝ)|^1063 ≤ (13524837427919/100000000000000 : ℝ)^807
        have hw : |(-1094837473/5000000000 : ℝ)|=(1094837473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175601113/10000000000 : ℝ)|^1063 ≤ (41997381698109/100000000000000 : ℝ)^807
        have hw : |(5175601113/10000000000 : ℝ)|=(5175601113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406049867/10000000000 : ℝ)|^1063 ≤ (8895556173167/20000000000000 : ℝ)^807
        have hw : |(5406049867/10000000000 : ℝ)|=(5406049867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_9 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2637241073/5000000000 : ℝ)*x 0 + (-514526957/2500000000 : ℝ)*x 1 + (33787811/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637241073/5000000000 : ℝ)^1063 ≤ (21528735612921/50000000000000 : ℝ)^807 := by
    have hnat : (2637241073 : ℕ)^1063*50000000000000^807 ≤ 21528735612921^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637241073 5000000000 21528735612921 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514526957/2500000000 : ℝ)^1063 ≤ (6232374526173/50000000000000 : ℝ)^807 := by
    have hnat : (514526957 : ℕ)^1063*50000000000000^807 ≤ 6232374526173^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514526957 2500000000 6232374526173 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33787811/62500000 : ℝ)^1063 ≤ (44477779706239/100000000000000 : ℝ)^807 := by
    have hnat : (33787811 : ℕ)^1063*100000000000000^807 ≤ 44477779706239^807*62500000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33787811 62500000 44477779706239 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637241073/5000000000 : ℝ), (-514526957/2500000000 : ℝ), (33787811/62500000 : ℝ)] ![(21528735612921/50000000000000 : ℝ), (6232374526173/50000000000000 : ℝ), (44477779706239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637241073/5000000000 : ℝ)|^1063 ≤ (21528735612921/50000000000000 : ℝ)^807
        have hw : |(2637241073/5000000000 : ℝ)|=(2637241073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514526957/2500000000 : ℝ)|^1063 ≤ (6232374526173/50000000000000 : ℝ)^807
        have hw : |(-514526957/2500000000 : ℝ)|=(514526957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33787811/62500000 : ℝ)|^1063 ≤ (44477779706239/100000000000000 : ℝ)^807
        have hw : |(33787811/62500000 : ℝ)|=(33787811/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_10 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1054896413/2000000000 : ℝ)*x 0 + (5406049949/10000000000 : ℝ)*x 1 + (-2058107681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054896413/2000000000 : ℝ)^1063 ≤ (10764367588713/25000000000000 : ℝ)^807 := by
    have hnat : (1054896413 : ℕ)^1063*25000000000000^807 ≤ 10764367588713^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054896413 2000000000 10764367588713 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406049949/10000000000 : ℝ)^1063 ≤ (44477781754497/100000000000000 : ℝ)^807 := by
    have hnat : (5406049949 : ℕ)^1063*100000000000000^807 ≤ 44477781754497^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406049949 10000000000 44477781754497 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058107681/10000000000 : ℝ)^1063 ≤ (12464747879631/100000000000000 : ℝ)^807 := by
    have hnat : (2058107681 : ℕ)^1063*100000000000000^807 ≤ 12464747879631^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058107681 10000000000 12464747879631 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054896413/2000000000 : ℝ), (5406049949/10000000000 : ℝ), (-2058107681/10000000000 : ℝ)] ![(10764367588713/25000000000000 : ℝ), (44477781754497/100000000000000 : ℝ), (12464747879631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054896413/2000000000 : ℝ)|^1063 ≤ (10764367588713/25000000000000 : ℝ)^807
        have hw : |(1054896413/2000000000 : ℝ)|=(1054896413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406049949/10000000000 : ℝ)|^1063 ≤ (44477781754497/100000000000000 : ℝ)^807
        have hw : |(5406049949/10000000000 : ℝ)|=(5406049949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058107681/10000000000 : ℝ)|^1063 ≤ (12464747879631/100000000000000 : ℝ)^807
        have hw : |(-2058107681/10000000000 : ℝ)|=(2058107681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_11 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2260759109/5000000000 : ℝ)*x 0 + (4252760653/10000000000 : ℝ)*x 1 + (42527603/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260759109/5000000000 : ℝ)^1063 ≤ (8787636754523/25000000000000 : ℝ)^807 := by
    have hnat : (2260759109 : ℕ)^1063*25000000000000^807 ≤ 8787636754523^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260759109 5000000000 8787636754523 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252760653/10000000000 : ℝ)^1063 ≤ (8106182063469/25000000000000 : ℝ)^807 := by
    have hnat : (4252760653 : ℕ)^1063*25000000000000^807 ≤ 8106182063469^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252760653 10000000000 8106182063469 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42527603/100000000 : ℝ)^1063 ≤ (8106181177171/25000000000000 : ℝ)^807 := by
    have hnat : (42527603 : ℕ)^1063*25000000000000^807 ≤ 8106181177171^807*100000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42527603 100000000 8106181177171 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2260759109/5000000000 : ℝ), (4252760653/10000000000 : ℝ), (42527603/100000000 : ℝ)] ![(8787636754523/25000000000000 : ℝ), (8106182063469/25000000000000 : ℝ), (8106181177171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2260759109/5000000000 : ℝ)|^1063 ≤ (8787636754523/25000000000000 : ℝ)^807
        have hw : |(2260759109/5000000000 : ℝ)|=(2260759109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252760653/10000000000 : ℝ)|^1063 ≤ (8106182063469/25000000000000 : ℝ)^807
        have hw : |(4252760653/10000000000 : ℝ)|=(4252760653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42527603/100000000 : ℝ)|^1063 ≤ (8106181177171/25000000000000 : ℝ)^807
        have hw : |(42527603/100000000 : ℝ)|=(42527603/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_12 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989469827/10000000000 : ℝ)*x 0 + (1095556401/2000000000 : ℝ)*x 1 + (1050534459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989469827/10000000000 : ℝ)^1063 ≤ (5960048843981/50000000000000 : ℝ)^807 := by
    have hnat : (1989469827 : ℕ)^1063*50000000000000^807 ≤ 5960048843981^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989469827 10000000000 5960048843981 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095556401/2000000000 : ℝ)^1063 ≤ (22628398889113/50000000000000 : ℝ)^807 := by
    have hnat : (1095556401 : ℕ)^1063*50000000000000^807 ≤ 22628398889113^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095556401 2000000000 22628398889113 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050534459/2000000000 : ℝ)^1063 ≤ (8564620903061/20000000000000 : ℝ)^807 := by
    have hnat : (1050534459 : ℕ)^1063*20000000000000^807 ≤ 8564620903061^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050534459 2000000000 8564620903061 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989469827/10000000000 : ℝ), (1095556401/2000000000 : ℝ), (1050534459/2000000000 : ℝ)] ![(5960048843981/50000000000000 : ℝ), (22628398889113/50000000000000 : ℝ), (8564620903061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989469827/10000000000 : ℝ)|^1063 ≤ (5960048843981/50000000000000 : ℝ)^807
        have hw : |(-1989469827/10000000000 : ℝ)|=(1989469827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095556401/2000000000 : ℝ)|^1063 ≤ (22628398889113/50000000000000 : ℝ)^807
        have hw : |(1095556401/2000000000 : ℝ)|=(1095556401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050534459/2000000000 : ℝ)|^1063 ≤ (8564620903061/20000000000000 : ℝ)^807
        have hw : |(1050534459/2000000000 : ℝ)|=(1050534459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_13 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2691222509/5000000000 : ℝ)*x 0 + (-2119243207/10000000000 : ℝ)*x 1 + (5252672543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691222509/5000000000 : ℝ)^1063 ≤ (22111072189411/50000000000000 : ℝ)^807 := by
    have hnat : (2691222509 : ℕ)^1063*50000000000000^807 ≤ 22111072189411^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691222509 5000000000 22111072189411 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119243207/10000000000 : ℝ)^1063 ≤ (809671777387/6250000000000 : ℝ)^807 := by
    have hnat : (2119243207 : ℕ)^1063*6250000000000^807 ≤ 809671777387^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119243207 10000000000 809671777387 6250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252672543/10000000000 : ℝ)^1063 ≤ (21411553589269/50000000000000 : ℝ)^807 := by
    have hnat : (5252672543 : ℕ)^1063*50000000000000^807 ≤ 21411553589269^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252672543 10000000000 21411553589269 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691222509/5000000000 : ℝ), (-2119243207/10000000000 : ℝ), (5252672543/10000000000 : ℝ)] ![(22111072189411/50000000000000 : ℝ), (809671777387/6250000000000 : ℝ), (21411553589269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691222509/5000000000 : ℝ)|^1063 ≤ (22111072189411/50000000000000 : ℝ)^807
        have hw : |(2691222509/5000000000 : ℝ)|=(2691222509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119243207/10000000000 : ℝ)|^1063 ≤ (809671777387/6250000000000 : ℝ)^807
        have hw : |(-2119243207/10000000000 : ℝ)|=(2119243207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252672543/10000000000 : ℝ)|^1063 ≤ (21411553589269/50000000000000 : ℝ)^807
        have hw : |(5252672543/10000000000 : ℝ)|=(5252672543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_14 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2691222871/5000000000 : ℝ)*x 0 + (656583911/1250000000 : ℝ)*x 1 + (-1059621953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691222871/5000000000 : ℝ)^1063 ≤ (22111076107087/50000000000000 : ℝ)^807 := by
    have hnat : (2691222871 : ℕ)^1063*50000000000000^807 ≤ 22111076107087^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691222871 5000000000 22111076107087 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656583911/1250000000 : ℝ)^1063 ≤ (5352886712661/12500000000000 : ℝ)^807 := by
    have hnat : (656583911 : ℕ)^1063*12500000000000^807 ≤ 5352886712661^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656583911 1250000000 5352886712661 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059621953/5000000000 : ℝ)^1063 ≤ (6477377033297/50000000000000 : ℝ)^807 := by
    have hnat : (1059621953 : ℕ)^1063*50000000000000^807 ≤ 6477377033297^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059621953 5000000000 6477377033297 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691222871/5000000000 : ℝ), (656583911/1250000000 : ℝ), (-1059621953/5000000000 : ℝ)] ![(22111076107087/50000000000000 : ℝ), (5352886712661/12500000000000 : ℝ), (6477377033297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691222871/5000000000 : ℝ)|^1063 ≤ (22111076107087/50000000000000 : ℝ)^807
        have hw : |(2691222871/5000000000 : ℝ)|=(2691222871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656583911/1250000000 : ℝ)|^1063 ≤ (5352886712661/12500000000000 : ℝ)^807
        have hw : |(656583911/1250000000 : ℝ)|=(656583911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059621953/5000000000 : ℝ)|^1063 ≤ (6477377033297/50000000000000 : ℝ)^807
        have hw : |(-1059621953/5000000000 : ℝ)|=(1059621953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_box_15 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1040850589/2500000000 : ℝ)*x 0 + (4431812247/10000000000 : ℝ)*x 1 + (4431812623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040850589/2500000000 : ℝ)^1063 ≤ (7882576186131/25000000000000 : ℝ)^807 := by
    have hnat : (1040850589 : ℕ)^1063*25000000000000^807 ≤ 7882576186131^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040850589 2500000000 7882576186131 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431812247/10000000000 : ℝ)^1063 ≤ (34234845708943/100000000000000 : ℝ)^807 := by
    have hnat : (4431812247 : ℕ)^1063*100000000000000^807 ≤ 34234845708943^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431812247 10000000000 34234845708943 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4431812623/10000000000 : ℝ)^1063 ≤ (8558712383713/25000000000000 : ℝ)^807 := by
    have hnat : (4431812623 : ℕ)^1063*25000000000000^807 ≤ 8558712383713^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431812623 10000000000 8558712383713 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040850589/2500000000 : ℝ), (4431812247/10000000000 : ℝ), (4431812623/10000000000 : ℝ)] ![(7882576186131/25000000000000 : ℝ), (34234845708943/100000000000000 : ℝ), (8558712383713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040850589/2500000000 : ℝ)|^1063 ≤ (7882576186131/25000000000000 : ℝ)^807
        have hw : |(1040850589/2500000000 : ℝ)|=(1040850589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431812247/10000000000 : ℝ)|^1063 ≤ (34234845708943/100000000000000 : ℝ)^807
        have hw : |(4431812247/10000000000 : ℝ)|=(4431812247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4431812623/10000000000 : ℝ)|^1063 ≤ (8558712383713/25000000000000 : ℝ)^807
        have hw : |(4431812623/10000000000 : ℝ)|=(4431812623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (917/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62839/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11769/20000 : ℝ) ∧ (79657/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16831/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (917/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (917/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (917/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (917/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (917/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (917/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2757/25000 : ℝ) ^ (4251/1024 : ℝ) ≤ (2118763352787827/20000000000000000000 : ℝ) := by
    have hpowers : (2757/25000 : ℝ)^4251 ≤ (2118763352787827/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2757 : ℕ)^4251*20000000000000000000^1024 ≤ 2118763352787827^1024*25000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2757 25000 2118763352787827 20000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2757/25000 : ℝ)) (X := (2118763352787827/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (917/6250 : ℝ) ^ (4251/1024 : ℝ) ≤ (1386280444719217/4000000000000000000 : ℝ) := by
    have hpowers : (917/6250 : ℝ)^4251 ≤ (1386280444719217/4000000000000000000 : ℝ)^1024 := by
      have hnat : (917 : ℕ)^4251*4000000000000000000^1024 ≤ 1386280444719217^1024*6250^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        917 6250 1386280444719217 4000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (917/6250 : ℝ)) (X := (1386280444719217/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002118763352787827/10000000000000000000 : ℝ) ≤ (2000102067241407/2000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (10002118763352787827/10000000000000000000 : ℝ)^1024 ≤ (2000102067241407/2000000000000000 : ℝ)^4251 := by
      have hnat : (10002118763352787827 : ℕ)^1024*2000000000000000^4251 ≤ 2000102067241407^4251*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002118763352787827 10000000000000000000 2000102067241407 2000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000102067241407/2000000000000000 : ℝ)) (X := (10002118763352787827/10000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501131270697047989/2500000000000000000 : ℝ) ≤ (5000544917564907/5000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (2501131270697047989/2500000000000000000 : ℝ)^1024 ≤ (5000544917564907/5000000000000000 : ℝ)^4251 := by
      have hnat : (2501131270697047989 : ℕ)^1024*5000000000000000^4251 ≤ 5000544917564907^4251*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501131270697047989 2500000000000000000 5000544917564907 5000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000544917564907/5000000000000000 : ℝ)) (X := (2501131270697047989/2500000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001386280444719217/2000000000000000000 : ℝ) ≤ (10001669334052593/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (2001386280444719217/2000000000000000000 : ℝ)^1024 ≤ (10001669334052593/10000000000000000 : ℝ)^4251 := by
      have hnat : (2001386280444719217 : ℕ)^1024*10000000000000000^4251 ≤ 10001669334052593^4251*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001386280444719217 2000000000000000000 10001669334052593 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001669334052593/10000000000000000 : ℝ)) (X := (2001386280444719217/2000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2118763352787827/20000000000000000000 : ℝ) ≤ ((9107269559224405479/9110000000000000000 : ℝ)+2*(579498922779/364400000000000 : ℝ)*(2757/25000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (9107269559224405479/9110000000000000000 : ℝ)+2*(579498922779/364400000000000 : ℝ)*(2757/25000 : ℝ)=(2000102067241407/2000000000000000 : ℝ) by norm_num, show 1+2*(2118763352787827/20000000000000000000 : ℝ)=(10002118763352787827/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1386280444719217/4000000000000000000 : ℝ)+(2118763352787827/20000000000000000000 : ℝ) ≤ ((9107269559224405479/9110000000000000000 : ℝ)+(579498922779/364400000000000 : ℝ)*((917/6250 : ℝ)+(2757/25000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (9107269559224405479/9110000000000000000 : ℝ)+(579498922779/364400000000000 : ℝ)*((917/6250 : ℝ)+(2757/25000 : ℝ))=(5000544917564907/5000000000000000 : ℝ) by norm_num, show 1+(1386280444719217/4000000000000000000 : ℝ)+(2118763352787827/20000000000000000000 : ℝ)=(2501131270697047989/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1386280444719217/4000000000000000000 : ℝ) ≤ ((9107269559224405479/9110000000000000000 : ℝ)+2*(579498922779/364400000000000 : ℝ)*(917/6250 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (9107269559224405479/9110000000000000000 : ℝ)+2*(579498922779/364400000000000 : ℝ)*(917/6250 : ℝ)=(10001669334052593/10000000000000000 : ℝ) by norm_num, show 1+2*(1386280444719217/4000000000000000000 : ℝ)=(2001386280444719217/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9107269559224405479/9110000000000000000 : ℝ)*(X 1 0+X 2 0)+(579498922779/364400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (917/6250 : ℝ)) (c := (9107269559224405479/9110000000000000000 : ℝ)) (alpha := (579498922779/364400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9107269559224405479/9110000000000000000 : ℝ)*(X 0 1+X 2 1)+(579498922779/364400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (917/6250 : ℝ)) (c := (9107269559224405479/9110000000000000000 : ℝ)) (alpha := (579498922779/364400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9107269559224405479/9110000000000000000 : ℝ)*(X 0 2+X 1 2)+(579498922779/364400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (917/6250 : ℝ)) (c := (9107269559224405479/9110000000000000000 : ℝ)) (alpha := (579498922779/364400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-383325699/2000000000 : ℝ)*X 0 0+(5392011917/10000000000 : ℝ)*X 0 1+(2696005973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284369111/10000000000 : ℝ)*X 1 0+(-2063836569/10000000000 : ℝ)*X 1 1+(5392012131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284369521/10000000000 : ℝ)*X 2 0+(674001471/1250000000 : ℝ)*X 2 1+(-2063836509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4489291447/10000000000 : ℝ)*X 0 0+(4269161453/10000000000 : ℝ)*X 0 1+(4269161613/10000000000 : ℝ)*X 0 2+(4489291447/10000000000 : ℝ)*X 1 0+(4269161453/10000000000 : ℝ)*X 1 1+(4269161613/10000000000 : ℝ)*X 1 2+(4489291447/10000000000 : ℝ)*X 2 0+(4269161453/10000000000 : ℝ)*X 2 1+(4269161613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2262077459/10000000000 : ℝ)*X 0 0+(657961831/1250000000 : ℝ)*X 0 1+(5263695127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687344863/5000000000 : ℝ)*X 1 0+(-2114957851/10000000000 : ℝ)*X 1 1+(5263694821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374689513/10000000000 : ℝ)*X 2 0+(5263695003/10000000000 : ℝ)*X 2 1+(-1057478947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2094797199/5000000000 : ℝ)*X 0 0+(276184669/625000000 : ℝ)*X 0 1+(1104738671/2500000000 : ℝ)*X 0 2+(2094797199/5000000000 : ℝ)*X 1 0+(276184669/625000000 : ℝ)*X 1 1+(1104738671/2500000000 : ℝ)*X 1 2+(2094797199/5000000000 : ℝ)*X 2 0+(276184669/625000000 : ℝ)*X 2 1+(1104738671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1094837473/5000000000 : ℝ)*X 0 0+(5175601113/10000000000 : ℝ)*X 0 1+(5406049867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637241073/5000000000 : ℝ)*X 1 0+(-514526957/2500000000 : ℝ)*X 1 1+(33787811/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1054896413/2000000000 : ℝ)*X 2 0+(5406049949/10000000000 : ℝ)*X 2 1+(-2058107681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2260759109/5000000000 : ℝ)*X 0 0+(4252760653/10000000000 : ℝ)*X 0 1+(42527603/100000000 : ℝ)*X 0 2+(2260759109/5000000000 : ℝ)*X 1 0+(4252760653/10000000000 : ℝ)*X 1 1+(42527603/100000000 : ℝ)*X 1 2+(2260759109/5000000000 : ℝ)*X 2 0+(4252760653/10000000000 : ℝ)*X 2 1+(42527603/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1989469827/10000000000 : ℝ)*X 0 0+(1095556401/2000000000 : ℝ)*X 0 1+(1050534459/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2691222509/5000000000 : ℝ)*X 1 0+(-2119243207/10000000000 : ℝ)*X 1 1+(5252672543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2691222871/5000000000 : ℝ)*X 2 0+(656583911/1250000000 : ℝ)*X 2 1+(-1059621953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1040850589/2500000000 : ℝ)*X 0 0+(4431812247/10000000000 : ℝ)*X 0 1+(4431812623/10000000000 : ℝ)*X 0 2+(1040850589/2500000000 : ℝ)*X 1 0+(4431812247/10000000000 : ℝ)*X 1 1+(4431812623/10000000000 : ℝ)*X 1 2+(1040850589/2500000000 : ℝ)*X 2 0+(4431812247/10000000000 : ℝ)*X 2 1+(4431812623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62839/100000 : ℝ) ≤ (-71555312202457838278264864219623/113875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14276253/100000000000000 : ℝ)*(lower0) + (19631597/100000000000000 : ℝ)*(upper1) + (29335951/50000000000000 : ℝ)*(lower4) + (716024567056793/25000000000000 : ℝ)*(major0) + (716024567056793/25000000000000 : ℝ)*(major1) + (716024567056793/25000000000000 : ℝ)*(major2) + (6990531673/100000000000000 : ℝ)*(sp1) + (135936769/3125000000000 : ℝ)*(sp2) + (1466184637/50000000000000 : ℝ)*(sp3) + (3874255887368279/100000000000000 : ℝ)*(sp4) + (1937128630767681/50000000000000 : ℝ)*(sp5) + (1937129951045213/50000000000000 : ℝ)*(sp6) + (234359365570217/12500000000000 : ℝ)*(sp7) + (1672939751/20000000000000 : ℝ)*(sp12) + (187487785693101/10000000000000 : ℝ)*(f.failure) + (1937132126033517/50000000000000 : ℝ)*(f.sum) + (10523263939947/4555000000000000000000000000 : ℝ)*base65 + (1589190747981293847/227750000000000000000000000000000 : ℝ)*base67 + (840475442801043847/227750000000000000000000000000000 : ℝ)*base69 + (284223767439293847/227750000000000000000000000000000 : ℝ)*base71 + (5029877425781/2277500000000000000000000000 : ℝ)*base73 + (160114176656793847/227750000000000000000000000000000 : ℝ)*base75 + (1108081199039043847/227750000000000000000000000000000 : ℝ)*base77 + (11362196129055043847/227750000000000000000000000000000 : ℝ)*base79 + (19638365038897/4555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (7765241/1000000000000000000000 : ℝ)*base90 + (7765241/1000000000000000000000 : ℝ)*base92 + (7765241/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11769/20000 : ℝ) ≤ (67012673185378970376956804259981/113875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40132421/100000000000000 : ℝ)*(upper0) + (25334371/100000000000000 : ℝ)*(lower1) + (12536881/50000000000000 : ℝ)*(lower3) + (97053323/100000000000000 : ℝ)*(upper4) + (732778607964971/25000000000000 : ℝ)*(major0) + (732778607964971/25000000000000 : ℝ)*(major1) + (732778607964971/25000000000000 : ℝ)*(major2) + (1961932726485333/50000000000000 : ℝ)*(sp0) + (1961929908046349/50000000000000 : ℝ)*(sp1) + (784770478692333/20000000000000 : ℝ)*(sp2) + (1918735640759383/100000000000000 : ℝ)*(sp3) + (352304873/6250000000000 : ℝ)*(sp5) + (13059509001/100000000000000 : ℝ)*(sp10) + (11912489419/100000000000000 : ℝ)*(sp11) + (959373776624401/50000000000000 : ℝ)*(f.failure) + (1961932726485333/50000000000000 : ℝ)*(f.sum) + (1189642138947/2277500000000000000000000000 : ℝ)*base65 + (1625405897684298891/227750000000000000000000000000000 : ℝ)*base68 + (557186812898548891/227750000000000000000000000000000 : ℝ)*base70 + (1901830618802048891/227750000000000000000000000000000 : ℝ)*base72 + (15858886997271/4555000000000000000000000000 : ℝ)*base74 + (818540671756048891/227750000000000000000000000000000 : ℝ)*base76 + (1979099653733048891/227750000000000000000000000000000 : ℝ)*base78 + (3591921915113548891/227750000000000000000000000000000 : ℝ)*base80 + (6592187709347/2277500000000000000000000000 : ℝ)*base81 + (41521459/5000000000000000000000 : ℝ)*base89 + (41521459/5000000000000000000000 : ℝ)*base91 + (41521459/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79657/100000 : ℝ) ≤ (90711701616661916306190848095221/113875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9603907/12500000000000 : ℝ)*(upper0) + (132018059/100000000000000 : ℝ)*(upper1) + (8155189/20000000000000 : ℝ)*(upper4) + (811276320460189/25000000000000 : ℝ)*(major0) + (811276320460189/25000000000000 : ℝ)*(major1) + (811276320460189/25000000000000 : ℝ)*(major2) + (104052779859/100000000000000 : ℝ)*(sp1) + (90418323793/50000000000000 : ℝ)*(sp2) + (1225490601/6250000000000 : ℝ)*(sp3) + (2124221639/50000000000000 : ℝ)*(sp4) + (2169681528607509/50000000000000 : ℝ)*(sp8) + (1084815813219609/25000000000000 : ℝ)*(sp9) + (433918646901071/10000000000000 : ℝ)*(sp10) + (531067661418871/25000000000000 : ℝ)*(sp11) + (21242902535251/1000000000000 : ℝ)*(f.failure) + (542420913207287/12500000000000 : ℝ)*(f.sum) + (13754787880639/4555000000000000000000000000 : ℝ)*base66 + (1277844529029250531/227750000000000000000000000000000 : ℝ)*base67 + (1405154400863750531/227750000000000000000000000000000 : ℝ)*base69 + (2642826212929000531/227750000000000000000000000000000 : ℝ)*base71 + (7419231856731/1138750000000000000000000000 : ℝ)*base74 + (1165188807102000531/227750000000000000000000000000000 : ℝ)*base75 + (1027713526963750531/227750000000000000000000000000000 : ℝ)*base77 + (2718259730214250531/227750000000000000000000000000000 : ℝ)*base79 + (17066741089089/4555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (208391/100000000000000000000 : ℝ)*base90 + (208391/100000000000000000000 : ℝ)*base92 + (208391/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-16831/20000 : ℝ) ≤ (-479142606379518920818954611/569375000000000000000000000 : ℝ) := by norm_num
    linear_combination (158836883/100000000000000 : ℝ)*(upper3) + (135611357/100000000000000 : ℝ)*(lower4) + (90867013/50000000000000 : ℝ)*(upper5) + (410127954247233/12500000000000 : ℝ)*(major0) + (410127954247233/12500000000000 : ℝ)*(major1) + (410127954247233/12500000000000 : ℝ)*(major2) + (2737731227/20000000000000 : ℝ)*(sp4) + (14460880653/25000000000000 : ℝ)*(sp5) + (323670734613/50000000000000 : ℝ)*(sp6) + (90094329171/50000000000000 : ℝ)*(sp7) + (2221140737321313/50000000000000 : ℝ)*(sp12) + (88844746395523/2000000000000 : ℝ)*(sp13) + (2220823910914767/50000000000000 : ℝ)*(sp14) + (1073811354453887/50000000000000 : ℝ)*(sp15) + (536950724391529/25000000000000 : ℝ)*(f.failure) + (4442295163298761/100000000000000 : ℝ)*(f.sum) + (28015191862101/4555000000000000000000000000 : ℝ)*base66 + (197534465978964607/113875000000000000000000000000000 : ℝ)*base67 + (262514429068410393/113875000000000000000000000000000 : ℝ)*base70 + (90094324605535393/113875000000000000000000000000000 : ℝ)*base72 + (4153115981697/2277500000000000000000000000 : ℝ)*base73 + (899945807850535393/113875000000000000000000000000000 : ℝ)*base76 + (1149461679607714607/113875000000000000000000000000000 : ℝ)*base77 + (672838824796464607/113875000000000000000000000000000 : ℝ)*base79 + (1867283704281/284687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (13892411/2500000000000000000000 : ℝ)*base89 + (13892411/2500000000000000000000 : ℝ)*base91 + (13892411/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1292_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (917/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16831/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1292_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1292_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16831/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1292_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1292_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1292_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5507/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11769/20000 : ℝ) else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (16831/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1292_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
