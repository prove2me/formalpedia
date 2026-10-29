-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1689_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:50.842749+00:00
-- url     : https://prove2.me/submissions/7c19ec5e-7f0c-42cb-910c-496a79428a3a

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
theorem support_rectangle_w1689_s0_0 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-175097181/1250000000 : ℝ)*x 0 + (2870953923/5000000000 : ℝ)*x 1 + (617084717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175097181/1250000000 : ℝ)^5135 ≤ (2146249000529/25000000000000 : ℝ)^4111 := by
    have hnat : (175097181 : ℕ)^5135*25000000000000^4111 ≤ 2146249000529^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175097181 1250000000 2146249000529 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2870953923/5000000000 : ℝ)^5135 ≤ (12502016478401/25000000000000 : ℝ)^4111 := by
    have hnat : (2870953923 : ℕ)^5135*25000000000000^4111 ≤ 12502016478401^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870953923 5000000000 12502016478401 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617084717/1250000000 : ℝ)^5135 ≤ (20703469033193/50000000000000 : ℝ)^4111 := by
    have hnat : (617084717 : ℕ)^5135*50000000000000^4111 ≤ 20703469033193^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617084717 1250000000 20703469033193 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175097181/1250000000 : ℝ), (2870953923/5000000000 : ℝ), (617084717/1250000000 : ℝ)] ![(2146249000529/25000000000000 : ℝ), (12502016478401/25000000000000 : ℝ), (20703469033193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175097181/1250000000 : ℝ)|^5135 ≤ (2146249000529/25000000000000 : ℝ)^4111
        have hw : |(-175097181/1250000000 : ℝ)|=(175097181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2870953923/5000000000 : ℝ)|^5135 ≤ (12502016478401/25000000000000 : ℝ)^4111
        have hw : |(2870953923/5000000000 : ℝ)|=(2870953923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617084717/1250000000 : ℝ)|^5135 ≤ (20703469033193/50000000000000 : ℝ)^4111
        have hw : |(617084717/1250000000 : ℝ)|=(617084717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_1 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (677416867/1250000000 : ℝ)*x 0 + (-114997321/625000000 : ℝ)*x 1 + (4936678901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677416867/1250000000 : ℝ)^5135 ≤ (46523800218663/100000000000000 : ℝ)^4111 := by
    have hnat : (677416867 : ℕ)^5135*100000000000000^4111 ≤ 46523800218663^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677416867 1250000000 46523800218663 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114997321/625000000 : ℝ)^5135 ≤ (12069249488491/100000000000000 : ℝ)^4111 := by
    have hnat : (114997321 : ℕ)^5135*100000000000000^4111 ≤ 12069249488491^4111*625000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114997321 625000000 12069249488491 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4936678901/10000000000 : ℝ)^5135 ≤ (41406950271933/100000000000000 : ℝ)^4111 := by
    have hnat : (4936678901 : ℕ)^5135*100000000000000^4111 ≤ 41406950271933^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936678901 10000000000 41406950271933 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677416867/1250000000 : ℝ), (-114997321/625000000 : ℝ), (4936678901/10000000000 : ℝ)] ![(46523800218663/100000000000000 : ℝ), (12069249488491/100000000000000 : ℝ), (41406950271933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677416867/1250000000 : ℝ)|^5135 ≤ (46523800218663/100000000000000 : ℝ)^4111
        have hw : |(677416867/1250000000 : ℝ)|=(677416867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114997321/625000000 : ℝ)|^5135 ≤ (12069249488491/100000000000000 : ℝ)^4111
        have hw : |(-114997321/625000000 : ℝ)|=(114997321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4936678901/10000000000 : ℝ)|^5135 ≤ (41406950271933/100000000000000 : ℝ)^4111
        have hw : |(4936678901/10000000000 : ℝ)|=(4936678901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_2 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84677143/156250000 : ℝ)*x 0 + (2468338903/5000000000 : ℝ)*x 1 + (-919977819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84677143/156250000 : ℝ)^5135 ≤ (1453869499411/3125000000000 : ℝ)^4111 := by
    have hnat : (84677143 : ℕ)^5135*3125000000000^4111 ≤ 1453869499411^4111*156250000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84677143 156250000 1453869499411 3125000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2468338903/5000000000 : ℝ)^5135 ≤ (41406938799767/100000000000000 : ℝ)^4111 := by
    have hnat : (2468338903 : ℕ)^5135*100000000000000^4111 ≤ 41406938799767^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468338903 5000000000 41406938799767 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919977819/5000000000 : ℝ)^5135 ≤ (603461860737/5000000000000 : ℝ)^4111 := by
    have hnat : (919977819 : ℕ)^5135*5000000000000^4111 ≤ 603461860737^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919977819 5000000000 603461860737 5000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84677143/156250000 : ℝ), (2468338903/5000000000 : ℝ), (-919977819/5000000000 : ℝ)] ![(1453869499411/3125000000000 : ℝ), (41406938799767/100000000000000 : ℝ), (603461860737/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84677143/156250000 : ℝ)|^5135 ≤ (1453869499411/3125000000000 : ℝ)^4111
        have hw : |(84677143/156250000 : ℝ)|=(84677143/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2468338903/5000000000 : ℝ)|^5135 ≤ (41406938799767/100000000000000 : ℝ)^4111
        have hw : |(2468338903/5000000000 : ℝ)|=(2468338903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919977819/5000000000 : ℝ)|^5135 ≤ (603461860737/5000000000000 : ℝ)^4111
        have hw : |(-919977819/5000000000 : ℝ)|=(919977819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_3 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (405750709/1000000000 : ℝ)*x 0 + (1523468133/5000000000 : ℝ)*x 1 + (2634987411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405750709/1000000000 : ℝ)^5135 ≤ (32410180515281/100000000000000 : ℝ)^4111 := by
    have hnat : (405750709 : ℕ)^5135*100000000000000^4111 ≤ 32410180515281^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405750709 1000000000 32410180515281 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1523468133/5000000000 : ℝ)^5135 ≤ (22662093421367/100000000000000 : ℝ)^4111 := by
    have hnat : (1523468133 : ℕ)^5135*100000000000000^4111 ≤ 22662093421367^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523468133 5000000000 22662093421367 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2634987411/5000000000 : ℝ)^5135 ≤ (2807982878121/6250000000000 : ℝ)^4111 := by
    have hnat : (2634987411 : ℕ)^5135*6250000000000^4111 ≤ 2807982878121^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634987411 5000000000 2807982878121 6250000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(405750709/1000000000 : ℝ), (1523468133/5000000000 : ℝ), (2634987411/5000000000 : ℝ)] ![(32410180515281/100000000000000 : ℝ), (22662093421367/100000000000000 : ℝ), (2807982878121/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(405750709/1000000000 : ℝ)|^5135 ≤ (32410180515281/100000000000000 : ℝ)^4111
        have hw : |(405750709/1000000000 : ℝ)|=(405750709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1523468133/5000000000 : ℝ)|^5135 ≤ (22662093421367/100000000000000 : ℝ)^4111
        have hw : |(1523468133/5000000000 : ℝ)|=(1523468133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2634987411/5000000000 : ℝ)|^5135 ≤ (2807982878121/6250000000000 : ℝ)^4111
        have hw : |(2634987411/5000000000 : ℝ)|=(2634987411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_4 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1402806637/10000000000 : ℝ)*x 0 + (4956911051/10000000000 : ℝ)*x 1 + (1430243563/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1402806637/10000000000 : ℝ)^5135 ≤ (4300266457757/50000000000000 : ℝ)^4111 := by
    have hnat : (1402806637 : ℕ)^5135*50000000000000^4111 ≤ 4300266457757^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402806637 10000000000 4300266457757 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4956911051/10000000000 : ℝ)^5135 ≤ (20809513926729/50000000000000 : ℝ)^4111 := by
    have hnat : (4956911051 : ℕ)^5135*50000000000000^4111 ≤ 20809513926729^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4956911051 10000000000 20809513926729 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1430243563/2500000000 : ℝ)^5135 ≤ (4978043922061/10000000000000 : ℝ)^4111 := by
    have hnat : (1430243563 : ℕ)^5135*10000000000000^4111 ≤ 4978043922061^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430243563 2500000000 4978043922061 10000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1402806637/10000000000 : ℝ), (4956911051/10000000000 : ℝ), (1430243563/2500000000 : ℝ)] ![(4300266457757/50000000000000 : ℝ), (20809513926729/50000000000000 : ℝ), (4978043922061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1402806637/10000000000 : ℝ)|^5135 ≤ (4300266457757/50000000000000 : ℝ)^4111
        have hw : |(-1402806637/10000000000 : ℝ)|=(1402806637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4956911051/10000000000 : ℝ)|^5135 ≤ (20809513926729/50000000000000 : ℝ)^4111
        have hw : |(4956911051/10000000000 : ℝ)|=(4956911051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1430243563/2500000000 : ℝ)|^5135 ≤ (4978043922061/10000000000000 : ℝ)^4111
        have hw : |(1430243563/2500000000 : ℝ)|=(1430243563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_5 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200568123/10000000000 : ℝ)*x 0 + (-1055660933/10000000000 : ℝ)*x 1 + (2860487367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200568123/10000000000 : ℝ)^5135 ≤ (44189847394663/100000000000000 : ℝ)^4111 := by
    have hnat : (5200568123 : ℕ)^5135*100000000000000^4111 ≤ 44189847394663^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200568123 10000000000 44189847394663 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055660933/10000000000 : ℝ)^5135 ≤ (6029708129391/100000000000000 : ℝ)^4111 := by
    have hnat : (1055660933 : ℕ)^5135*100000000000000^4111 ≤ 6029708129391^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055660933 10000000000 6029708129391 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2860487367/5000000000 : ℝ)^5135 ≤ (49780444459373/100000000000000 : ℝ)^4111 := by
    have hnat : (2860487367 : ℕ)^5135*100000000000000^4111 ≤ 49780444459373^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2860487367 5000000000 49780444459373 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200568123/10000000000 : ℝ), (-1055660933/10000000000 : ℝ), (2860487367/5000000000 : ℝ)] ![(44189847394663/100000000000000 : ℝ), (6029708129391/100000000000000 : ℝ), (49780444459373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200568123/10000000000 : ℝ)|^5135 ≤ (44189847394663/100000000000000 : ℝ)^4111
        have hw : |(5200568123/10000000000 : ℝ)|=(5200568123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1055660933/10000000000 : ℝ)|^5135 ≤ (6029708129391/100000000000000 : ℝ)^4111
        have hw : |(-1055660933/10000000000 : ℝ)|=(1055660933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2860487367/5000000000 : ℝ)|^5135 ≤ (49780444459373/100000000000000 : ℝ)^4111
        have hw : |(2860487367/5000000000 : ℝ)|=(2860487367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_6 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520056823/1000000000 : ℝ)*x 0 + (5720974791/10000000000 : ℝ)*x 1 + (-65978793/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520056823/1000000000 : ℝ)^5135 ≤ (44189848530323/100000000000000 : ℝ)^4111 := by
    have hnat : (520056823 : ℕ)^5135*100000000000000^4111 ≤ 44189848530323^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520056823 1000000000 44189848530323 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720974791/10000000000 : ℝ)^5135 ≤ (9956089015779/20000000000000 : ℝ)^4111 := by
    have hnat : (5720974791 : ℕ)^5135*20000000000000^4111 ≤ 9956089015779^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720974791 10000000000 9956089015779 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65978793/625000000 : ℝ)^5135 ≤ (6029706381433/100000000000000 : ℝ)^4111 := by
    have hnat : (65978793 : ℕ)^5135*100000000000000^4111 ≤ 6029706381433^4111*625000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65978793 625000000 6029706381433 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520056823/1000000000 : ℝ), (5720974791/10000000000 : ℝ), (-65978793/625000000 : ℝ)] ![(44189848530323/100000000000000 : ℝ), (9956089015779/20000000000000 : ℝ), (6029706381433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520056823/1000000000 : ℝ)|^5135 ≤ (44189848530323/100000000000000 : ℝ)^4111
        have hw : |(520056823/1000000000 : ℝ)|=(520056823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720974791/10000000000 : ℝ)|^5135 ≤ (9956089015779/20000000000000 : ℝ)^4111
        have hw : |(5720974791/10000000000 : ℝ)|=(5720974791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65978793/625000000 : ℝ)|^5135 ≤ (6029706381433/100000000000000 : ℝ)^4111
        have hw : |(-65978793/625000000 : ℝ)|=(65978793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s0_7 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (507888579/1250000000 : ℝ)*x 0 + (5214114587/10000000000 : ℝ)*x 1 + (1552363559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507888579/1250000000 : ℝ)^5135 ≤ (16233039328453/50000000000000 : ℝ)^4111 := by
    have hnat : (507888579 : ℕ)^5135*50000000000000^4111 ≤ 16233039328453^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507888579 1250000000 16233039328453 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214114587/10000000000 : ℝ)^5135 ≤ (8866734281807/20000000000000 : ℝ)^4111 := by
    have hnat : (5214114587 : ℕ)^5135*20000000000000^4111 ≤ 8866734281807^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214114587 10000000000 8866734281807 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552363559/5000000000 : ℝ)^5135 ≤ (23200249920133/100000000000000 : ℝ)^4111 := by
    have hnat : (1552363559 : ℕ)^5135*100000000000000^4111 ≤ 23200249920133^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552363559 5000000000 23200249920133 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(507888579/1250000000 : ℝ), (5214114587/10000000000 : ℝ), (1552363559/5000000000 : ℝ)] ![(16233039328453/50000000000000 : ℝ), (8866734281807/20000000000000 : ℝ), (23200249920133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(507888579/1250000000 : ℝ)|^5135 ≤ (16233039328453/50000000000000 : ℝ)^4111
        have hw : |(507888579/1250000000 : ℝ)|=(507888579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214114587/10000000000 : ℝ)|^5135 ≤ (8866734281807/20000000000000 : ℝ)^4111
        have hw : |(5214114587/10000000000 : ℝ)|=(5214114587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1552363559/5000000000 : ℝ)|^5135 ≤ (23200249920133/100000000000000 : ℝ)^4111
        have hw : |(1552363559/5000000000 : ℝ)|=(1552363559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1689_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22677/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5127/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5127 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5127*1^1024 ≤ 0^1024*1^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5127/1024 : ℝ) ≤ (101760601081678753/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5127 ≤ (101760601081678753/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5127*10000000000000000000^1024 ≤ 101760601081678753^1024*5^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 101760601081678753 10000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (101760601081678753/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5127 := by
      have hnat : (1 : ℕ)^1024*1^5127 ≤ 1^5127*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10101760601081678753/10000000000000000000 : ℝ) ≤ (10020242077938169/10000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (10101760601081678753/10000000000000000000 : ℝ)^1024 ≤ (10020242077938169/10000000000000000 : ℝ)^5127 := by
      have hnat : (10101760601081678753 : ℕ)^1024*10000000000000000^5127 ≤ 10020242077938169^5127*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10101760601081678753 10000000000000000000 10020242077938169 10000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020242077938169/10000000000000000 : ℝ)) (X := (10101760601081678753/10000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5101760601081678753/5000000000000000000 : ℝ) ≤ (5020242077938169/5000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (5101760601081678753/5000000000000000000 : ℝ)^1024 ≤ (5020242077938169/5000000000000000 : ℝ)^5127 := by
      have hnat : (5101760601081678753 : ℕ)^1024*5000000000000000^5127 ≤ 5020242077938169^5127*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5101760601081678753 5000000000000000000 5020242077938169 5000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020242077938169/5000000000000000 : ℝ)) (X := (5101760601081678753/5000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(20242077938169/4000000000000000 : ℝ)*(0 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20242077938169/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(101760601081678753/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(20242077938169/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5127/1024 : ℝ) := by
    rw [show (1 : ℝ)+(20242077938169/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10020242077938169/10000000000000000 : ℝ) by norm_num, show 1+(101760601081678753/10000000000000000000 : ℝ)+(0 : ℝ)=(10101760601081678753/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(101760601081678753/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(20242077938169/4000000000000000 : ℝ)*(2/5 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(20242077938169/4000000000000000 : ℝ)*(2/5 : ℝ)=(5020242077938169/5000000000000000 : ℝ) by norm_num, show 1+2*(101760601081678753/10000000000000000000 : ℝ)=(5101760601081678753/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(20242077938169/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20242077938169/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(20242077938169/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20242077938169/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(20242077938169/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (20242077938169/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-175097181/1250000000 : ℝ)*X 0 0+(2870953923/5000000000 : ℝ)*X 0 1+(617084717/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677416867/1250000000 : ℝ)*X 1 0+(-114997321/625000000 : ℝ)*X 1 1+(4936678901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((84677143/156250000 : ℝ)*X 2 0+(2468338903/5000000000 : ℝ)*X 2 1+(-919977819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((405750709/1000000000 : ℝ)*X 0 0+(1523468133/5000000000 : ℝ)*X 0 1+(2634987411/5000000000 : ℝ)*X 0 2+(405750709/1000000000 : ℝ)*X 1 0+(1523468133/5000000000 : ℝ)*X 1 1+(2634987411/5000000000 : ℝ)*X 1 2+(405750709/1000000000 : ℝ)*X 2 0+(1523468133/5000000000 : ℝ)*X 2 1+(2634987411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1402806637/10000000000 : ℝ)*X 0 0+(4956911051/10000000000 : ℝ)*X 0 1+(1430243563/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5200568123/10000000000 : ℝ)*X 1 0+(-1055660933/10000000000 : ℝ)*X 1 1+(2860487367/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((520056823/1000000000 : ℝ)*X 2 0+(5720974791/10000000000 : ℝ)*X 2 1+(-65978793/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((507888579/1250000000 : ℝ)*X 0 0+(5214114587/10000000000 : ℝ)*X 0 1+(1552363559/5000000000 : ℝ)*X 0 2+(507888579/1250000000 : ℝ)*X 1 0+(5214114587/10000000000 : ℝ)*X 1 1+(1552363559/5000000000 : ℝ)*X 1 2+(507888579/1250000000 : ℝ)*X 2 0+(5214114587/10000000000 : ℝ)*X 2 1+(1552363559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50359034442155376480903/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252935899/50000000000000 : ℝ)*(base19) + (168454163/20000000000000 : ℝ)*(base23) + (20837653/12500000000000 : ℝ)*(base24) + (2555519/100000000000000 : ℝ)*(upper4) + (10828657/10000000000000 : ℝ)*(upper5) + (211465881433629/25000000000000 : ℝ)*(major0) + (211465881433629/25000000000000 : ℝ)*(major1) + (211465881433629/25000000000000 : ℝ)*(major2) + (4851109144447/390625000000 : ℝ)*(sp0) + (310472136415921/25000000000000 : ℝ)*(sp1) + (620944021281721/50000000000000 : ℝ)*(sp2) + (449836260208361/100000000000000 : ℝ)*(sp3) + (102211141/2000000000000 : ℝ)*(sp4) + (200679303/12500000000000 : ℝ)*(sp7) + (89967573128557/20000000000000 : ℝ)*(f.failure) + (1241889051535481/100000000000000 : ℝ)*(f.sum) + (216473114314699/50000000000000000000000000000 : ℝ)*base66 + (279493854314699/100000000000000000000000000000 : ℝ)*base68 + (781380193314699/100000000000000000000000000000 : ℝ)*base70 + (867553028914699/100000000000000000000000000000 : ℝ)*base72 + (159835444785301/50000000000000000000000000000 : ℝ)*base73 + (1192086666514699/100000000000000000000000000000 : ℝ)*base76 + (321546324914699/100000000000000000000000000000 : ℝ)*base78 + (273476977314699/100000000000000000000000000000 : ℝ)*base80 + (188214399614699/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6430027/1000000000000000000000 : ℝ)*base89 + (6430027/1000000000000000000000 : ℝ)*base91 + (6430027/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68331936999529697985249/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177266037/12500000000000 : ℝ)*(base19) + (376168983/25000000000000 : ℝ)*(base23) + (1992851/12500000000000 : ℝ)*(upper2) + (267831263/100000000000000 : ℝ)*(upper3) + (27504919/12500000000000 : ℝ)*(upper5) + (44571585489107/5000000000000 : ℝ)*(major0) + (44571585489107/5000000000000 : ℝ)*(major1) + (44571585489107/5000000000000 : ℝ)*(major2) + (1025310001/20000000000000 : ℝ)*(sp1) + (5815027271/100000000000000 : ℝ)*(sp2) + (1308791754148203/100000000000000 : ℝ)*(sp4) + (654392604734951/50000000000000 : ℝ)*(sp5) + (261756886889/20000000000 : ℝ)*(sp6) + (9481428752859/2000000000000 : ℝ)*(sp7) + (9481428752859/2000000000000 : ℝ)*(f.failure) + (1308791754148203/100000000000000 : ℝ)*(f.sum) + (17947241864917/10000000000000000000000000000 : ℝ)*base66 + (165637908965083/20000000000000000000000000000 : ℝ)*base67 + (102089776094917/20000000000000000000000000000 : ℝ)*base70 + (2430908505083/20000000000000000000000000000 : ℝ)*base71 + (20828094985083/10000000000000000000000000000 : ℝ)*base73 + (60596404434917/20000000000000000000000000000 : ℝ)*base76 + (17353362814917/20000000000000000000000000000 : ℝ)*base78 + (74358887505083/20000000000000000000000000000 : ℝ)*base79 + (42339572994917/10000000000000000000000000000 : ℝ)*base82 + (744749/100000000000000000000 : ℝ)*base89 + (744749/100000000000000000000 : ℝ)*base91 + (744749/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1689_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1689_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1689_s1_0 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1485992809/10000000000 : ℝ)*x 0 + (344173301/625000000 : ℝ)*x 1 + (1279009481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1485992809/10000000000 : ℝ)^5135 ≤ (2310554244641/25000000000000 : ℝ)^4111 := by
    have hnat : (1485992809 : ℕ)^5135*25000000000000^4111 ≤ 2310554244641^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485992809 10000000000 2310554244641 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344173301/625000000 : ℝ)^5135 ≤ (47463285763049/100000000000000 : ℝ)^4111 := by
    have hnat : (344173301 : ℕ)^5135*100000000000000^4111 ≤ 47463285763049^4111*625000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344173301 625000000 47463285763049 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279009481/2500000000 : ℝ)^5135 ≤ (43294497238199/100000000000000 : ℝ)^4111 := by
    have hnat : (1279009481 : ℕ)^5135*100000000000000^4111 ≤ 43294497238199^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279009481 2500000000 43294497238199 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1485992809/10000000000 : ℝ), (344173301/625000000 : ℝ), (1279009481/2500000000 : ℝ)] ![(2310554244641/25000000000000 : ℝ), (47463285763049/100000000000000 : ℝ), (43294497238199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1485992809/10000000000 : ℝ)|^5135 ≤ (2310554244641/25000000000000 : ℝ)^4111
        have hw : |(-1485992809/10000000000 : ℝ)|=(1485992809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344173301/625000000 : ℝ)|^5135 ≤ (47463285763049/100000000000000 : ℝ)^4111
        have hw : |(344173301/625000000 : ℝ)|=(344173301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279009481/2500000000 : ℝ)|^5135 ≤ (43294497238199/100000000000000 : ℝ)^4111
        have hw : |(1279009481/2500000000 : ℝ)|=(1279009481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_1 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071338433/2000000000 : ℝ)*x 0 + (-844946451/5000000000 : ℝ)*x 1 + (639504707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071338433/2000000000 : ℝ)^5135 ≤ (45853042573851/100000000000000 : ℝ)^4111 := by
    have hnat : (1071338433 : ℕ)^5135*100000000000000^4111 ≤ 45853042573851^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071338433 2000000000 45853042573851 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844946451/5000000000 : ℝ)^5135 ≤ (542623150109/5000000000000 : ℝ)^4111 := by
    have hnat : (844946451 : ℕ)^5135*5000000000000^4111 ≤ 542623150109^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844946451 5000000000 542623150109 5000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639504707/1250000000 : ℝ)^5135 ≤ (43294494405329/100000000000000 : ℝ)^4111 := by
    have hnat : (639504707 : ℕ)^5135*100000000000000^4111 ≤ 43294494405329^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639504707 1250000000 43294494405329 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071338433/2000000000 : ℝ), (-844946451/5000000000 : ℝ), (639504707/1250000000 : ℝ)] ![(45853042573851/100000000000000 : ℝ), (542623150109/5000000000000 : ℝ), (43294494405329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071338433/2000000000 : ℝ)|^5135 ≤ (45853042573851/100000000000000 : ℝ)^4111
        have hw : |(1071338433/2000000000 : ℝ)|=(1071338433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844946451/5000000000 : ℝ)|^5135 ≤ (542623150109/5000000000000 : ℝ)^4111
        have hw : |(-844946451/5000000000 : ℝ)|=(844946451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639504707/1250000000 : ℝ)|^5135 ≤ (43294494405329/100000000000000 : ℝ)^4111
        have hw : |(639504707/1250000000 : ℝ)|=(639504707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_2 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26783457/50000000 : ℝ)*x 0 + (204641533/400000000 : ℝ)*x 1 + (-21123663/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26783457/50000000 : ℝ)^5135 ≤ (45853034394367/100000000000000 : ℝ)^4111 := by
    have hnat : (26783457 : ℕ)^5135*100000000000000^4111 ≤ 45853034394367^4111*50000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26783457 50000000 45853034394367 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204641533/400000000 : ℝ)^5135 ≤ (8658900295387/20000000000000 : ℝ)^4111 := by
    have hnat : (204641533 : ℕ)^5135*20000000000000^4111 ≤ 8658900295387^4111*400000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204641533 400000000 8658900295387 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21123663/125000000 : ℝ)^5135 ≤ (10852464109163/100000000000000 : ℝ)^4111 := by
    have hnat : (21123663 : ℕ)^5135*100000000000000^4111 ≤ 10852464109163^4111*125000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21123663 125000000 10852464109163 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26783457/50000000 : ℝ), (204641533/400000000 : ℝ), (-21123663/125000000 : ℝ)] ![(45853034394367/100000000000000 : ℝ), (8658900295387/20000000000000 : ℝ), (10852464109163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26783457/50000000 : ℝ)|^5135 ≤ (45853034394367/100000000000000 : ℝ)^4111
        have hw : |(26783457/50000000 : ℝ)|=(26783457/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(204641533/400000000 : ℝ)|^5135 ≤ (8658900295387/20000000000000 : ℝ)^4111
        have hw : |(204641533/400000000 : ℝ)|=(204641533/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21123663/125000000 : ℝ)|^5135 ≤ (10852464109163/100000000000000 : ℝ)^4111
        have hw : |(-21123663/125000000 : ℝ)|=(21123663/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_3 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2064116559/5000000000 : ℝ)*x 0 + (3612430359/10000000000 : ℝ)*x 1 + (4691150949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064116559/5000000000 : ℝ)^5135 ≤ (8279341005157/25000000000000 : ℝ)^4111 := by
    have hnat : (2064116559 : ℕ)^5135*25000000000000^4111 ≤ 8279341005157^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064116559 5000000000 8279341005157 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3612430359/10000000000 : ℝ)^5135 ≤ (7007978043129/25000000000000 : ℝ)^4111 := by
    have hnat : (3612430359 : ℕ)^5135*25000000000000^4111 ≤ 7007978043129^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3612430359 10000000000 7007978043129 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4691150949/10000000000 : ℝ)^5135 ≤ (19425361895223/50000000000000 : ℝ)^4111 := by
    have hnat : (4691150949 : ℕ)^5135*50000000000000^4111 ≤ 19425361895223^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4691150949 10000000000 19425361895223 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2064116559/5000000000 : ℝ), (3612430359/10000000000 : ℝ), (4691150949/10000000000 : ℝ)] ![(8279341005157/25000000000000 : ℝ), (7007978043129/25000000000000 : ℝ), (19425361895223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2064116559/5000000000 : ℝ)|^5135 ≤ (8279341005157/25000000000000 : ℝ)^4111
        have hw : |(2064116559/5000000000 : ℝ)|=(2064116559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3612430359/10000000000 : ℝ)|^5135 ≤ (7007978043129/25000000000000 : ℝ)^4111
        have hw : |(3612430359/10000000000 : ℝ)|=(3612430359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4691150949/10000000000 : ℝ)|^5135 ≤ (19425361895223/50000000000000 : ℝ)^4111
        have hw : |(4691150949/10000000000 : ℝ)|=(4691150949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_4 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-297244227/2000000000 : ℝ)*x 0 + (640099101/1250000000 : ℝ)*x 1 + (2750969237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (297244227/2000000000 : ℝ)^5135 ≤ (4621995412669/50000000000000 : ℝ)^4111 := by
    have hnat : (297244227 : ℕ)^5135*50000000000000^4111 ≤ 4621995412669^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297244227 2000000000 4621995412669 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640099101/1250000000 : ℝ)^5135 ≤ (270904775861/625000000000 : ℝ)^4111 := by
    have hnat : (640099101 : ℕ)^5135*625000000000^4111 ≤ 270904775861^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640099101 1250000000 270904775861 625000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750969237/5000000000 : ℝ)^5135 ≤ (47411245020449/100000000000000 : ℝ)^4111 := by
    have hnat : (2750969237 : ℕ)^5135*100000000000000^4111 ≤ 47411245020449^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750969237 5000000000 47411245020449 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-297244227/2000000000 : ℝ), (640099101/1250000000 : ℝ), (2750969237/5000000000 : ℝ)] ![(4621995412669/50000000000000 : ℝ), (270904775861/625000000000 : ℝ), (47411245020449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-297244227/2000000000 : ℝ)|^5135 ≤ (4621995412669/50000000000000 : ℝ)^4111
        have hw : |(-297244227/2000000000 : ℝ)|=(297244227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640099101/1250000000 : ℝ)|^5135 ≤ (270904775861/625000000000 : ℝ)^4111
        have hw : |(640099101/1250000000 : ℝ)|=(640099101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750969237/5000000000 : ℝ)|^5135 ≤ (47411245020449/100000000000000 : ℝ)^4111
        have hw : |(2750969237/5000000000 : ℝ)|=(2750969237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_5 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252167091/10000000000 : ℝ)*x 0 + (-1303994213/10000000000 : ℝ)*x 1 + (5501938619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252167091/10000000000 : ℝ)^5135 ≤ (44738175743299/100000000000000 : ℝ)^4111 := by
    have hnat : (5252167091 : ℕ)^5135*100000000000000^4111 ≤ 44738175743299^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252167091 10000000000 44738175743299 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303994213/10000000000 : ℝ)^5135 ≤ (3925288828357/50000000000000 : ℝ)^4111 := by
    have hnat : (1303994213 : ℕ)^5135*50000000000000^4111 ≤ 3925288828357^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303994213 10000000000 3925288828357 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501938619/10000000000 : ℝ)^5135 ≤ (1896449863247/4000000000000 : ℝ)^4111 := by
    have hnat : (5501938619 : ℕ)^5135*4000000000000^4111 ≤ 1896449863247^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501938619 10000000000 1896449863247 4000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252167091/10000000000 : ℝ), (-1303994213/10000000000 : ℝ), (5501938619/10000000000 : ℝ)] ![(44738175743299/100000000000000 : ℝ), (3925288828357/50000000000000 : ℝ), (1896449863247/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252167091/10000000000 : ℝ)|^5135 ≤ (44738175743299/100000000000000 : ℝ)^4111
        have hw : |(5252167091/10000000000 : ℝ)|=(5252167091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1303994213/10000000000 : ℝ)|^5135 ≤ (3925288828357/50000000000000 : ℝ)^4111
        have hw : |(-1303994213/10000000000 : ℝ)|=(1303994213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501938619/10000000000 : ℝ)|^5135 ≤ (1896449863247/4000000000000 : ℝ)^4111
        have hw : |(5501938619/10000000000 : ℝ)|=(5501938619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_6 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050433697/2000000000 : ℝ)*x 0 + (5501938069/10000000000 : ℝ)*x 1 + (-1303993029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050433697/2000000000 : ℝ)^5135 ≤ (8947638115031/20000000000000 : ℝ)^4111 := by
    have hnat : (1050433697 : ℕ)^5135*20000000000000^4111 ≤ 8947638115031^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050433697 2000000000 8947638115031 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501938069/10000000000 : ℝ)^5135 ≤ (2370562033059/5000000000000 : ℝ)^4111 := by
    have hnat : (5501938069 : ℕ)^5135*5000000000000^4111 ≤ 2370562033059^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501938069 10000000000 2370562033059 5000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303993029/10000000000 : ℝ)^5135 ≤ (7850568753013/100000000000000 : ℝ)^4111 := by
    have hnat : (1303993029 : ℕ)^5135*100000000000000^4111 ≤ 7850568753013^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303993029 10000000000 7850568753013 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050433697/2000000000 : ℝ), (5501938069/10000000000 : ℝ), (-1303993029/10000000000 : ℝ)] ![(8947638115031/20000000000000 : ℝ), (2370562033059/5000000000000 : ℝ), (7850568753013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050433697/2000000000 : ℝ)|^5135 ≤ (8947638115031/20000000000000 : ℝ)^4111
        have hw : |(1050433697/2000000000 : ℝ)|=(1050433697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501938069/10000000000 : ℝ)|^5135 ≤ (2370562033059/5000000000000 : ℝ)^4111
        have hw : |(5501938069/10000000000 : ℝ)|=(5501938069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1303993029/10000000000 : ℝ)|^5135 ≤ (7850568753013/100000000000000 : ℝ)^4111
        have hw : |(-1303993029/10000000000 : ℝ)|=(1303993029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s1_7 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128864569/10000000000 : ℝ)*x 0 + (935604569/2000000000 : ℝ)*x 1 + (725155501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128864569/10000000000 : ℝ)^5135 ≤ (33123691524909/100000000000000 : ℝ)^4111 := by
    have hnat : (4128864569 : ℕ)^5135*100000000000000^4111 ≤ 33123691524909^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128864569 10000000000 33123691524909 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935604569/2000000000 : ℝ)^5135 ≤ (38714966491929/100000000000000 : ℝ)^4111 := by
    have hnat : (935604569 : ℕ)^5135*100000000000000^4111 ≤ 38714966491929^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935604569 2000000000 38714966491929 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (725155501/2000000000 : ℝ)^5135 ≤ (14080670980033/50000000000000 : ℝ)^4111 := by
    have hnat : (725155501 : ℕ)^5135*50000000000000^4111 ≤ 14080670980033^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725155501 2000000000 14080670980033 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128864569/10000000000 : ℝ), (935604569/2000000000 : ℝ), (725155501/2000000000 : ℝ)] ![(33123691524909/100000000000000 : ℝ), (38714966491929/100000000000000 : ℝ), (14080670980033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128864569/10000000000 : ℝ)|^5135 ≤ (33123691524909/100000000000000 : ℝ)^4111
        have hw : |(4128864569/10000000000 : ℝ)|=(4128864569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(935604569/2000000000 : ℝ)|^5135 ≤ (38714966491929/100000000000000 : ℝ)^4111
        have hw : |(935604569/2000000000 : ℝ)|=(935604569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(725155501/2000000000 : ℝ)|^5135 ≤ (14080670980033/50000000000000 : ℝ)^4111
        have hw : |(725155501/2000000000 : ℝ)|=(725155501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1689_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4703/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5399/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (11241928509423/25000000000000000000 : ℝ) := by
    have hpowers : (5399/100000 : ℝ)^5127 ≤ (11241928509423/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5399 : ℕ)^5127*25000000000000000000^1024 ≤ 11241928509423^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5399 100000 11241928509423 25000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5399/100000 : ℝ)) (X := (11241928509423/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22677/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (59363954527376817/100000000000000000000 : ℝ) := by
    have hpowers : (22677/100000 : ℝ)^5127 ≤ (59363954527376817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22677 : ℕ)^5127*100000000000000000000^1024 ≤ 59363954527376817^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22677 100000 59363954527376817 100000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22677/100000 : ℝ)) (X := (59363954527376817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500011241928509423/12500000000000000000 : ℝ) ≤ (10000001796252101/10000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (12500011241928509423/12500000000000000000 : ℝ)^1024 ≤ (10000001796252101/10000000000000000 : ℝ)^5127 := by
      have hnat : (12500011241928509423 : ℕ)^1024*10000000000000000^5127 ≤ 10000001796252101^5127*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500011241928509423 12500000000000000000 10000001796252101 10000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001796252101/10000000000000000 : ℝ)) (X := (12500011241928509423/12500000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100059408922241414509/100000000000000000000 : ℝ) ≤ (2500296568559049/2500000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (100059408922241414509/100000000000000000000 : ℝ)^1024 ≤ (2500296568559049/2500000000000000 : ℝ)^5127 := by
      have hnat : (100059408922241414509 : ℕ)^1024*2500000000000000^5127 ≤ 2500296568559049^5127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100059408922241414509 100000000000000000000 2500296568559049 2500000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500296568559049/2500000000000000 : ℝ)) (X := (100059408922241414509/100000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50059363954527376817/50000000000000000000 : ℝ) ≤ (10002370752220291/10000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (50059363954527376817/50000000000000000000 : ℝ)^1024 ≤ (10002370752220291/10000000000000000 : ℝ)^5127 := by
      have hnat : (50059363954527376817 : ℕ)^1024*10000000000000000^5127 ≤ 10002370752220291^5127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059363954527376817 50000000000000000000 10002370752220291 10000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002370752220291/10000000000000000 : ℝ)) (X := (50059363954527376817/50000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11241928509423/25000000000000000000 : ℝ) ≤ ((43191810260592885817/43195000000000000000 : ℝ)+2*(236895596819/345560000000000 : ℝ)*(5399/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (43191810260592885817/43195000000000000000 : ℝ)+2*(236895596819/345560000000000 : ℝ)*(5399/100000 : ℝ)=(10000001796252101/10000000000000000 : ℝ) by norm_num, show 1+2*(11241928509423/25000000000000000000 : ℝ)=(12500011241928509423/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59363954527376817/100000000000000000000 : ℝ)+(11241928509423/25000000000000000000 : ℝ) ≤ ((43191810260592885817/43195000000000000000 : ℝ)+(236895596819/345560000000000 : ℝ)*((22677/100000 : ℝ)+(5399/100000 : ℝ)))^(5127/1024 : ℝ) := by
    rw [show (43191810260592885817/43195000000000000000 : ℝ)+(236895596819/345560000000000 : ℝ)*((22677/100000 : ℝ)+(5399/100000 : ℝ))=(2500296568559049/2500000000000000 : ℝ) by norm_num, show 1+(59363954527376817/100000000000000000000 : ℝ)+(11241928509423/25000000000000000000 : ℝ)=(100059408922241414509/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59363954527376817/100000000000000000000 : ℝ) ≤ ((43191810260592885817/43195000000000000000 : ℝ)+2*(236895596819/345560000000000 : ℝ)*(22677/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (43191810260592885817/43195000000000000000 : ℝ)+2*(236895596819/345560000000000 : ℝ)*(22677/100000 : ℝ)=(10002370752220291/10000000000000000 : ℝ) by norm_num, show 1+2*(59363954527376817/100000000000000000000 : ℝ)=(50059363954527376817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43191810260592885817/43195000000000000000 : ℝ)*(X 1 0+X 2 0)+(236895596819/345560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (5399/100000 : ℝ)) (hi := (22677/100000 : ℝ)) (c := (43191810260592885817/43195000000000000000 : ℝ)) (alpha := (236895596819/345560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43191810260592885817/43195000000000000000 : ℝ)*(X 0 1+X 2 1)+(236895596819/345560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (5399/100000 : ℝ)) (hi := (22677/100000 : ℝ)) (c := (43191810260592885817/43195000000000000000 : ℝ)) (alpha := (236895596819/345560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43191810260592885817/43195000000000000000 : ℝ)*(X 0 2+X 1 2)+(236895596819/345560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (5399/100000 : ℝ)) (hi := (22677/100000 : ℝ)) (c := (43191810260592885817/43195000000000000000 : ℝ)) (alpha := (236895596819/345560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1485992809/10000000000 : ℝ)*X 0 0+(344173301/625000000 : ℝ)*X 0 1+(1279009481/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071338433/2000000000 : ℝ)*X 1 0+(-844946451/5000000000 : ℝ)*X 1 1+(639504707/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26783457/50000000 : ℝ)*X 2 0+(204641533/400000000 : ℝ)*X 2 1+(-21123663/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2064116559/5000000000 : ℝ)*X 0 0+(3612430359/10000000000 : ℝ)*X 0 1+(4691150949/10000000000 : ℝ)*X 0 2+(2064116559/5000000000 : ℝ)*X 1 0+(3612430359/10000000000 : ℝ)*X 1 1+(4691150949/10000000000 : ℝ)*X 1 2+(2064116559/5000000000 : ℝ)*X 2 0+(3612430359/10000000000 : ℝ)*X 2 1+(4691150949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-297244227/2000000000 : ℝ)*X 0 0+(640099101/1250000000 : ℝ)*X 0 1+(2750969237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252167091/10000000000 : ℝ)*X 1 0+(-1303994213/10000000000 : ℝ)*X 1 1+(5501938619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050433697/2000000000 : ℝ)*X 2 0+(5501938069/10000000000 : ℝ)*X 2 1+(-1303993029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4128864569/10000000000 : ℝ)*X 0 0+(935604569/2000000000 : ℝ)*X 0 1+(725155501/2000000000 : ℝ)*X 0 2+(4128864569/10000000000 : ℝ)*X 1 0+(935604569/2000000000 : ℝ)*X 1 1+(725155501/2000000000 : ℝ)*X 1 2+(4128864569/10000000000 : ℝ)*X 2 0+(935604569/2000000000 : ℝ)*X 2 1+(725155501/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1151532969035432884093696851/269968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606276277/100000000000000 : ℝ)*(base19) + (13164521/5000000000000 : ℝ)*(base23) + (27384147/100000000000000 : ℝ)*(upper2) + (59691327/50000000000000 : ℝ)*(upper3) + (7662773/50000000000000 : ℝ)*(upper4) + (435789502790651/25000000000000 : ℝ)*(major0) + (435789502790651/25000000000000 : ℝ)*(major1) + (435789502790651/25000000000000 : ℝ)*(major2) + (1279642948871377/50000000000000 : ℝ)*(sp0) + (1279644046760767/50000000000000 : ℝ)*(sp1) + (255928843650739/10000000000000 : ℝ)*(sp2) + (927025506004893/100000000000000 : ℝ)*(sp3) + (175128441/6250000000000 : ℝ)*(sp4) + (1674341477/100000000000000 : ℝ)*(sp7) + (92702718034637/10000000000000 : ℝ)*(f.failure) + (255928869979781/10000000000000 : ℝ)*(f.sum) + (107372838993661/8639000000000000000000000000 : ℝ)*base66 + (1696021641819721867/1079875000000000000000000000000000 : ℝ)*base67 + (5216468180318028133/1079875000000000000000000000000000 : ℝ)*base70 + (5996527025478653133/1079875000000000000000000000000000 : ℝ)*base72 + (6230780213219/4319500000000000000000000000 : ℝ)*base74 + (19533512552305028133/1079875000000000000000000000000000 : ℝ)*base76 + (9897969498567403133/1079875000000000000000000000000000 : ℝ)*base78 + (3177140246565528133/1079875000000000000000000000000000 : ℝ)*base80 + (157296447549/43195000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4092907/500000000000000000000 : ℝ)*base89 + (4092907/500000000000000000000 : ℝ)*base91 + (4092907/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15399995819958115853793536067/2159750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139146373/50000000000000 : ℝ)*(base23) + (159908193/100000000000000 : ℝ)*(lower2) + (38043323/100000000000000 : ℝ)*(upper3) + (85531283/100000000000000 : ℝ)*(upper4) + (251259759/100000000000000 : ℝ)*(upper5) + (1787013898420583/100000000000000 : ℝ)*(major0) + (1787013898420583/100000000000000 : ℝ)*(major1) + (1787013898420583/100000000000000 : ℝ)*(major2) + (1237187213/50000000000000 : ℝ)*(sp2) + (526142613/100000000000000 : ℝ)*(sp3) + (655919355429189/25000000000000 : ℝ)*(sp4) + (655919355429189/25000000000000 : ℝ)*(sp5) + (2623674669049583/100000000000000 : ℝ)*(sp6) + (950349611300019/100000000000000 : ℝ)*(sp7) + (118793767180329/12500000000000 : ℝ)*(f.failure) + (655919355429189/25000000000000 : ℝ)*(f.sum) + (162164800468847/17278000000000000000000000000 : ℝ)*base65 + (27441967964131196311/4319500000000000000000000000000000 : ℝ)*base67 + (31462274755935803689/4319500000000000000000000000000000 : ℝ)*base70 + (25389998253396696311/4319500000000000000000000000000000 : ℝ)*base71 + (6372058511869/3455600000000000000000000000 : ℝ)*base73 + (14827576249525803689/4319500000000000000000000000000000 : ℝ)*base76 + (32808085708196196311/4319500000000000000000000000000000 : ℝ)*base77 + (55802678313265696311/4319500000000000000000000000000000 : ℝ)*base79 + (50991540906553/17278000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6614081/625000000000000000000 : ℝ)*base90 + (6614081/625000000000000000000 : ℝ)*base92 + (6614081/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1689_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1689_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1689_s2_0 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1491432271/10000000000 : ℝ)*x 0 + (274249799/500000000 : ℝ)*x 1 + (513419913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1491432271/10000000000 : ℝ)^5135 ≤ (9284494170711/100000000000000 : ℝ)^4111 := by
    have hnat : (1491432271 : ℕ)^5135*100000000000000^4111 ≤ 9284494170711^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491432271 10000000000 9284494170711 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274249799/500000000 : ℝ)^5135 ≤ (11807238085879/25000000000000 : ℝ)^4111 := by
    have hnat : (274249799 : ℕ)^5135*25000000000000^4111 ≤ 11807238085879^4111*500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274249799 500000000 11807238085879 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513419913/1000000000 : ℝ)^5135 ≤ (43486553466589/100000000000000 : ℝ)^4111 := by
    have hnat : (513419913 : ℕ)^5135*100000000000000^4111 ≤ 43486553466589^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513419913 1000000000 43486553466589 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1491432271/10000000000 : ℝ), (274249799/500000000 : ℝ), (513419913/1000000000 : ℝ)] ![(9284494170711/100000000000000 : ℝ), (11807238085879/25000000000000 : ℝ), (43486553466589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1491432271/10000000000 : ℝ)|^5135 ≤ (9284494170711/100000000000000 : ℝ)^4111
        have hw : |(-1491432271/10000000000 : ℝ)|=(1491432271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274249799/500000000 : ℝ)|^5135 ≤ (11807238085879/25000000000000 : ℝ)^4111
        have hw : |(274249799/500000000 : ℝ)|=(274249799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513419913/1000000000 : ℝ)|^5135 ≤ (43486553466589/100000000000000 : ℝ)^4111
        have hw : |(513419913/1000000000 : ℝ)|=(513419913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_1 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350856923/10000000000 : ℝ)*x 0 + (-10460673/62500000 : ℝ)*x 1 + (641774893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350856923/10000000000 : ℝ)^5135 ≤ (45790659844593/100000000000000 : ℝ)^4111 := by
    have hnat : (5350856923 : ℕ)^5135*100000000000000^4111 ≤ 45790659844593^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350856923 10000000000 45790659844593 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10460673/62500000 : ℝ)^5135 ≤ (83771769823/781250000000 : ℝ)^4111 := by
    have hnat : (10460673 : ℕ)^5135*781250000000^4111 ≤ 83771769823^4111*62500000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10460673 62500000 83771769823 781250000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641774893/1250000000 : ℝ)^5135 ≤ (21743276807353/50000000000000 : ℝ)^4111 := by
    have hnat : (641774893 : ℕ)^5135*50000000000000^4111 ≤ 21743276807353^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641774893 1250000000 21743276807353 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350856923/10000000000 : ℝ), (-10460673/62500000 : ℝ), (641774893/1250000000 : ℝ)] ![(45790659844593/100000000000000 : ℝ), (83771769823/781250000000 : ℝ), (21743276807353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350856923/10000000000 : ℝ)|^5135 ≤ (45790659844593/100000000000000 : ℝ)^4111
        have hw : |(5350856923/10000000000 : ℝ)|=(5350856923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10460673/62500000 : ℝ)|^5135 ≤ (83771769823/781250000000 : ℝ)^4111
        have hw : |(-10460673/62500000 : ℝ)|=(10460673/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641774893/1250000000 : ℝ)|^5135 ≤ (21743276807353/50000000000000 : ℝ)^4111
        have hw : |(641774893/1250000000 : ℝ)|=(641774893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_2 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350856969/10000000000 : ℝ)*x 0 + (5134199069/10000000000 : ℝ)*x 1 + (-1673707717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350856969/10000000000 : ℝ)^5135 ≤ (22895330168149/50000000000000 : ℝ)^4111 := by
    have hnat : (5350856969 : ℕ)^5135*50000000000000^4111 ≤ 22895330168149^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350856969 10000000000 22895330168149 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134199069/10000000000 : ℝ)^5135 ≤ (1739462112849/4000000000000 : ℝ)^4111 := by
    have hnat : (5134199069 : ℕ)^5135*4000000000000^4111 ≤ 1739462112849^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134199069 10000000000 1739462112849 4000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1673707717/10000000000 : ℝ)^5135 ≤ (5361393416717/50000000000000 : ℝ)^4111 := by
    have hnat : (1673707717 : ℕ)^5135*50000000000000^4111 ≤ 5361393416717^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673707717 10000000000 5361393416717 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350856969/10000000000 : ℝ), (5134199069/10000000000 : ℝ), (-1673707717/10000000000 : ℝ)] ![(22895330168149/50000000000000 : ℝ), (1739462112849/4000000000000 : ℝ), (5361393416717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350856969/10000000000 : ℝ)|^5135 ≤ (22895330168149/50000000000000 : ℝ)^4111
        have hw : |(5350856969/10000000000 : ℝ)|=(5350856969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134199069/10000000000 : ℝ)|^5135 ≤ (1739462112849/4000000000000 : ℝ)^4111
        have hw : |(5134199069/10000000000 : ℝ)|=(5134199069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1673707717/10000000000 : ℝ)|^5135 ≤ (5361393416717/50000000000000 : ℝ)^4111
        have hw : |(-1673707717/10000000000 : ℝ)|=(1673707717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_3 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1033103709/2500000000 : ℝ)*x 0 + (3667169461/10000000000 : ℝ)*x 1 + (57945393/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033103709/2500000000 : ℝ)^5135 ≤ (33159271740643/100000000000000 : ℝ)^4111 := by
    have hnat : (1033103709 : ℕ)^5135*100000000000000^4111 ≤ 33159271740643^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033103709 2500000000 33159271740643 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3667169461/10000000000 : ℝ)^5135 ≤ (5712696230843/20000000000000 : ℝ)^4111 := by
    have hnat : (3667169461 : ℕ)^5135*20000000000000^4111 ≤ 5712696230843^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3667169461 10000000000 5712696230843 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57945393/125000000 : ℝ)^5135 ≤ (38277247092433/100000000000000 : ℝ)^4111 := by
    have hnat : (57945393 : ℕ)^5135*100000000000000^4111 ≤ 38277247092433^4111*125000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57945393 125000000 38277247092433 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033103709/2500000000 : ℝ), (3667169461/10000000000 : ℝ), (57945393/125000000 : ℝ)] ![(33159271740643/100000000000000 : ℝ), (5712696230843/20000000000000 : ℝ), (38277247092433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033103709/2500000000 : ℝ)|^5135 ≤ (33159271740643/100000000000000 : ℝ)^4111
        have hw : |(1033103709/2500000000 : ℝ)|=(1033103709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3667169461/10000000000 : ℝ)|^5135 ≤ (5712696230843/20000000000000 : ℝ)^4111
        have hw : |(3667169461/10000000000 : ℝ)|=(3667169461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57945393/125000000 : ℝ)|^5135 ≤ (38277247092433/100000000000000 : ℝ)^4111
        have hw : |(57945393/125000000 : ℝ)|=(57945393/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_4 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-745798849/5000000000 : ℝ)*x 0 + (5138035603/10000000000 : ℝ)*x 1 + (5481101853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745798849/5000000000 : ℝ)^5135 ≤ (2321445130863/25000000000000 : ℝ)^4111 := by
    have hnat : (745798849 : ℕ)^5135*25000000000000^4111 ≤ 2321445130863^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745798849 5000000000 2321445130863 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138035603/10000000000 : ℝ)^5135 ≤ (43527146154071/100000000000000 : ℝ)^4111 := by
    have hnat : (5138035603 : ℕ)^5135*100000000000000^4111 ≤ 43527146154071^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138035603 10000000000 43527146154071 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481101853/10000000000 : ℝ)^5135 ≤ (23593536653997/50000000000000 : ℝ)^4111 := by
    have hnat : (5481101853 : ℕ)^5135*50000000000000^4111 ≤ 23593536653997^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481101853 10000000000 23593536653997 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-745798849/5000000000 : ℝ), (5138035603/10000000000 : ℝ), (5481101853/10000000000 : ℝ)] ![(2321445130863/25000000000000 : ℝ), (43527146154071/100000000000000 : ℝ), (23593536653997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-745798849/5000000000 : ℝ)|^5135 ≤ (2321445130863/25000000000000 : ℝ)^4111
        have hw : |(-745798849/5000000000 : ℝ)|=(745798849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138035603/10000000000 : ℝ)|^5135 ≤ (43527146154071/100000000000000 : ℝ)^4111
        have hw : |(5138035603/10000000000 : ℝ)|=(5138035603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481101853/10000000000 : ℝ)|^5135 ≤ (23593536653997/50000000000000 : ℝ)^4111
        have hw : |(5481101853/10000000000 : ℝ)|=(5481101853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_5 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628539309/5000000000 : ℝ)*x 0 + (-20731327/156250000 : ℝ)*x 1 + (5481101901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628539309/5000000000 : ℝ)^5135 ≤ (447904394021/1000000000000 : ℝ)^4111 := by
    have hnat : (2628539309 : ℕ)^5135*1000000000000^4111 ≤ 447904394021^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628539309 5000000000 447904394021 1000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20731327/156250000 : ℝ)^5135 ≤ (4011243376961/50000000000000 : ℝ)^4111 := by
    have hnat : (20731327 : ℕ)^5135*50000000000000^4111 ≤ 4011243376961^4111*156250000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20731327 156250000 4011243376961 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481101901/10000000000 : ℝ)^5135 ≤ (294919211401/625000000000 : ℝ)^4111 := by
    have hnat : (5481101901 : ℕ)^5135*625000000000^4111 ≤ 294919211401^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481101901 10000000000 294919211401 625000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628539309/5000000000 : ℝ), (-20731327/156250000 : ℝ), (5481101901/10000000000 : ℝ)] ![(447904394021/1000000000000 : ℝ), (4011243376961/50000000000000 : ℝ), (294919211401/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628539309/5000000000 : ℝ)|^5135 ≤ (447904394021/1000000000000 : ℝ)^4111
        have hw : |(2628539309/5000000000 : ℝ)|=(2628539309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20731327/156250000 : ℝ)|^5135 ≤ (4011243376961/50000000000000 : ℝ)^4111
        have hw : |(-20731327/156250000 : ℝ)|=(20731327/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481101901/10000000000 : ℝ)|^5135 ≤ (294919211401/625000000000 : ℝ)^4111
        have hw : |(5481101901/10000000000 : ℝ)|=(5481101901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_6 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257078607/10000000000 : ℝ)*x 0 + (2740550951/5000000000 : ℝ)*x 1 + (-1326804943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257078607/10000000000 : ℝ)^5135 ≤ (8958087857007/20000000000000 : ℝ)^4111 := by
    have hnat : (5257078607 : ℕ)^5135*20000000000000^4111 ≤ 8958087857007^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257078607 10000000000 8958087857007 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740550951/5000000000 : ℝ)^5135 ≤ (47187073834913/100000000000000 : ℝ)^4111 := by
    have hnat : (2740550951 : ℕ)^5135*100000000000000^4111 ≤ 47187073834913^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740550951 5000000000 47187073834913 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1326804943/10000000000 : ℝ)^5135 ≤ (8022486867211/100000000000000 : ℝ)^4111 := by
    have hnat : (1326804943 : ℕ)^5135*100000000000000^4111 ≤ 8022486867211^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326804943 10000000000 8022486867211 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257078607/10000000000 : ℝ), (2740550951/5000000000 : ℝ), (-1326804943/10000000000 : ℝ)] ![(8958087857007/20000000000000 : ℝ), (47187073834913/100000000000000 : ℝ), (8022486867211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257078607/10000000000 : ℝ)|^5135 ≤ (8958087857007/20000000000000 : ℝ)^4111
        have hw : |(5257078607/10000000000 : ℝ)|=(5257078607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740550951/5000000000 : ℝ)|^5135 ≤ (47187073834913/100000000000000 : ℝ)^4111
        have hw : |(2740550951/5000000000 : ℝ)|=(2740550951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1326804943/10000000000 : ℝ)|^5135 ≤ (8022486867211/100000000000000 : ℝ)^4111
        have hw : |(-1326804943/10000000000 : ℝ)|=(1326804943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s2_7 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2066435753/5000000000 : ℝ)*x 0 + (4625039813/10000000000 : ℝ)*x 1 + (1838960091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066435753/5000000000 : ℝ)^5135 ≤ (4145481121023/12500000000000 : ℝ)^4111 := by
    have hnat : (2066435753 : ℕ)^5135*12500000000000^4111 ≤ 4145481121023^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066435753 5000000000 4145481121023 12500000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4625039813/10000000000 : ℝ)^5135 ≤ (9542009187221/25000000000000 : ℝ)^4111 := by
    have hnat : (4625039813 : ℕ)^5135*25000000000000^4111 ≤ 9542009187221^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625039813 10000000000 9542009187221 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1838960091/5000000000 : ℝ)^5135 ≤ (5733622853177/20000000000000 : ℝ)^4111 := by
    have hnat : (1838960091 : ℕ)^5135*20000000000000^4111 ≤ 5733622853177^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838960091 5000000000 5733622853177 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066435753/5000000000 : ℝ), (4625039813/10000000000 : ℝ), (1838960091/5000000000 : ℝ)] ![(4145481121023/12500000000000 : ℝ), (9542009187221/25000000000000 : ℝ), (5733622853177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066435753/5000000000 : ℝ)|^5135 ≤ (4145481121023/12500000000000 : ℝ)^4111
        have hw : |(2066435753/5000000000 : ℝ)|=(2066435753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4625039813/10000000000 : ℝ)|^5135 ≤ (9542009187221/25000000000000 : ℝ)^4111
        have hw : |(4625039813/10000000000 : ℝ)|=(4625039813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1838960091/5000000000 : ℝ)|^5135 ≤ (5733622853177/20000000000000 : ℝ)^4111
        have hw : |(1838960091/5000000000 : ℝ)|=(1838960091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1689_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9801/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8633/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4703/50000 : ℝ) ^ (5127/1024 : ℝ) ≤ (181111964479221/25000000000000000000 : ℝ) := by
    have hpowers : (4703/50000 : ℝ)^5127 ≤ (181111964479221/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4703 : ℕ)^5127*25000000000000000000^1024 ≤ 181111964479221^1024*50000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4703 50000 181111964479221 25000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4703/50000 : ℝ)) (X := (181111964479221/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17721/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (863522871114281/5000000000000000000 : ℝ) := by
    have hpowers : (17721/100000 : ℝ)^5127 ≤ (863522871114281/5000000000000000000 : ℝ)^1024 := by
      have hnat : (17721 : ℕ)^5127*5000000000000000000^1024 ≤ 863522871114281^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17721 100000 863522871114281 5000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17721/100000 : ℝ)) (X := (863522871114281/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500181111964479221/12500000000000000000 : ℝ) ≤ (2500007234545599/2500000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (12500181111964479221/12500000000000000000 : ℝ)^1024 ≤ (2500007234545599/2500000000000000 : ℝ)^5127 := by
      have hnat : (12500181111964479221 : ℕ)^1024*2500000000000000^5127 ≤ 2500007234545599^5127*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500181111964479221 12500000000000000000 2500007234545599 2500000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007234545599/2500000000000000 : ℝ)) (X := (12500181111964479221/12500000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502249363160025313/12500000000000000000 : ℝ) ≤ (10000359380853221/10000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (12502249363160025313/12500000000000000000 : ℝ)^1024 ≤ (10000359380853221/10000000000000000 : ℝ)^5127 := by
      have hnat : (12502249363160025313 : ℕ)^1024*10000000000000000^5127 ≤ 10000359380853221^5127*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502249363160025313 12500000000000000000 10000359380853221 10000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000359380853221/10000000000000000 : ℝ)) (X := (12502249363160025313/12500000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2500863522871114281/2500000000000000000 : ℝ) ≤ (5000344911762023/5000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (2500863522871114281/2500000000000000000 : ℝ)^1024 ≤ (5000344911762023/5000000000000000 : ℝ)^5127 := by
      have hnat : (2500863522871114281 : ℕ)^1024*5000000000000000^5127 ≤ 5000344911762023^5127*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500863522871114281 2500000000000000000 5000344911762023 5000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344911762023/5000000000000000 : ℝ)) (X := (2500863522871114281/2500000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(181111964479221/25000000000000000000 : ℝ) ≤ ((2078600608336576571/2078750000000000000 : ℝ)+2*(13217706833/33260000000000 : ℝ)*(4703/50000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (2078600608336576571/2078750000000000000 : ℝ)+2*(13217706833/33260000000000 : ℝ)*(4703/50000 : ℝ)=(2500007234545599/2500000000000000 : ℝ) by norm_num, show 1+2*(181111964479221/25000000000000000000 : ℝ)=(12500181111964479221/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(863522871114281/5000000000000000000 : ℝ)+(181111964479221/25000000000000000000 : ℝ) ≤ ((2078600608336576571/2078750000000000000 : ℝ)+(13217706833/33260000000000 : ℝ)*((17721/100000 : ℝ)+(4703/50000 : ℝ)))^(5127/1024 : ℝ) := by
    rw [show (2078600608336576571/2078750000000000000 : ℝ)+(13217706833/33260000000000 : ℝ)*((17721/100000 : ℝ)+(4703/50000 : ℝ))=(10000359380853221/10000000000000000 : ℝ) by norm_num, show 1+(863522871114281/5000000000000000000 : ℝ)+(181111964479221/25000000000000000000 : ℝ)=(12502249363160025313/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(863522871114281/5000000000000000000 : ℝ) ≤ ((2078600608336576571/2078750000000000000 : ℝ)+2*(13217706833/33260000000000 : ℝ)*(17721/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (2078600608336576571/2078750000000000000 : ℝ)+2*(13217706833/33260000000000 : ℝ)*(17721/100000 : ℝ)=(5000344911762023/5000000000000000 : ℝ) by norm_num, show 1+2*(863522871114281/5000000000000000000 : ℝ)=(2500863522871114281/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2078600608336576571/2078750000000000000 : ℝ)*(X 1 0+X 2 0)+(13217706833/33260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (4703/50000 : ℝ)) (hi := (17721/100000 : ℝ)) (c := (2078600608336576571/2078750000000000000 : ℝ)) (alpha := (13217706833/33260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2078600608336576571/2078750000000000000 : ℝ)*(X 0 1+X 2 1)+(13217706833/33260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (4703/50000 : ℝ)) (hi := (17721/100000 : ℝ)) (c := (2078600608336576571/2078750000000000000 : ℝ)) (alpha := (13217706833/33260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2078600608336576571/2078750000000000000 : ℝ)*(X 0 2+X 1 2)+(13217706833/33260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (4703/50000 : ℝ)) (hi := (17721/100000 : ℝ)) (c := (2078600608336576571/2078750000000000000 : ℝ)) (alpha := (13217706833/33260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1491432271/10000000000 : ℝ)*X 0 0+(274249799/500000000 : ℝ)*X 0 1+(513419913/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350856923/10000000000 : ℝ)*X 1 0+(-10460673/62500000 : ℝ)*X 1 1+(641774893/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350856969/10000000000 : ℝ)*X 2 0+(5134199069/10000000000 : ℝ)*X 2 1+(-1673707717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1033103709/2500000000 : ℝ)*X 0 0+(3667169461/10000000000 : ℝ)*X 0 1+(57945393/125000000 : ℝ)*X 0 2+(1033103709/2500000000 : ℝ)*X 1 0+(3667169461/10000000000 : ℝ)*X 1 1+(57945393/125000000 : ℝ)*X 1 2+(1033103709/2500000000 : ℝ)*X 2 0+(3667169461/10000000000 : ℝ)*X 2 1+(57945393/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-745798849/5000000000 : ℝ)*X 0 0+(5138035603/10000000000 : ℝ)*X 0 1+(5481101853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628539309/5000000000 : ℝ)*X 1 0+(-20731327/156250000 : ℝ)*X 1 1+(5481101901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257078607/10000000000 : ℝ)*X 2 0+(2740550951/5000000000 : ℝ)*X 2 1+(-1326804943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2066435753/5000000000 : ℝ)*X 0 0+(4625039813/10000000000 : ℝ)*X 0 1+(1838960091/5000000000 : ℝ)*X 0 2+(2066435753/5000000000 : ℝ)*X 1 0+(4625039813/10000000000 : ℝ)*X 1 1+(1838960091/5000000000 : ℝ)*X 1 2+(2066435753/5000000000 : ℝ)*X 2 0+(4625039813/10000000000 : ℝ)*X 2 1+(1838960091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277257071219298730064298279/103937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48794237/12500000000000 : ℝ)*(base19) + (370854333/100000000000000 : ℝ)*(base23) + (5886743/25000000000000 : ℝ)*(lower2) + (74472949/100000000000000 : ℝ)*(upper3) + (22862797/100000000000000 : ℝ)*(upper5) + (1941614064709761/100000000000000 : ℝ)*(major0) + (1941614064709761/100000000000000 : ℝ)*(major1) + (1941614064709761/100000000000000 : ℝ)*(major2) + (285065669424961/10000000000000 : ℝ)*(sp0) + (1425329873704401/50000000000000 : ℝ)*(sp1) + (712664941727091/25000000000000 : ℝ)*(sp2) + (129070783431279/12500000000000 : ℝ)*(sp3) + (13451223/390625000000 : ℝ)*(sp4) + (1635288703/100000000000000 : ℝ)*(sp7) + (206513580547787/20000000000000 : ℝ)*(f.failure) + (2850660137762697/100000000000000 : ℝ)*(f.sum) + (1817170922869/332600000000000000000000000 : ℝ)*base65 + (1909855675145952969/207875000000000000000000000000000 : ℝ)*base68 + (1103976691921577969/207875000000000000000000000000000 : ℝ)*base70 + (1102144383138827969/207875000000000000000000000000000 : ℝ)*base72 + (412643295253/83150000000000000000000000 : ℝ)*base73 + (2416722725448077969/207875000000000000000000000000000 : ℝ)*base76 + (187692377840077969/207875000000000000000000000000000 : ℝ)*base78 + (652227152405452969/207875000000000000000000000000000 : ℝ)*base80 + (1681928994719/1663000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2357443/1000000000000000000000 : ℝ)*base90 + (2357443/1000000000000000000000 : ℝ)*base92 + (2357443/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (297635583804816697315309803/25984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (804199579/50000000000000 : ℝ)*(base19) + (108961577/6250000000000 : ℝ)*(base23) + (60926373/25000000000000 : ℝ)*(upper3) + (64036583/100000000000000 : ℝ)*(lower4) + (14763477/6250000000000 : ℝ)*(upper5) + (496340126689977/25000000000000 : ℝ)*(major0) + (496340126689977/25000000000000 : ℝ)*(major1) + (496340126689977/25000000000000 : ℝ)*(major2) + (114638503/800000000000 : ℝ)*(sp1) + (15410334139/100000000000000 : ℝ)*(sp2) + (291488797582147/10000000000000 : ℝ)*(sp4) + (1457436018804719/50000000000000 : ℝ)*(sp5) + (29148708221021/1000000000000 : ℝ)*(sp6) + (82486926241/7812500000 : ℝ)*(sp7) + (82486926241/7812500000 : ℝ)*(f.failure) + (291488797582147/10000000000000 : ℝ)*(f.sum) + (398559388093/207875000000000000000000000 : ℝ)*base65 + (471843585190896133/51968750000000000000000000000000 : ℝ)*base68 + (30300387631521133/51968750000000000000000000000000 : ℝ)*base70 + (293666142917052383/51968750000000000000000000000000 : ℝ)*base72 + (1026327129551/415750000000000000000000000 : ℝ)*base74 + (664752386964771133/51968750000000000000000000000000 : ℝ)*base76 + (768320594584739883/51968750000000000000000000000000 : ℝ)*base78 + (334080373178489883/51968750000000000000000000000000 : ℝ)*base80 + (6122057166033/1663000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2363/195312500000000000 : ℝ)*base89 + (2363/195312500000000000 : ℝ)*base91 + (2363/195312500000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1689_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1689_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1689_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1689_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1689_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1689_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1689_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
