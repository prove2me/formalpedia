-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1606_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:18.207735+00:00
-- url     : https://prove2.me/submissions/a159ffe5-d5c1-46eb-83e9-395542ec91de

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
theorem support_rectangle_w1606_s0_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-49159663/312500000 : ℝ)*x 0 + (2921280761/5000000000 : ℝ)*x 1 + (2445000751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49159663/312500000 : ℝ)^4743 ≤ (9453490402849/100000000000000 : ℝ)^3719 := by
    have hnat : (49159663 : ℕ)^4743*100000000000000^3719 ≤ 9453490402849^3719*312500000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49159663 312500000 9453490402849 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2921280761/5000000000 : ℝ)^4743 ≤ (50389399608459/100000000000000 : ℝ)^3719 := by
    have hnat : (2921280761 : ℕ)^4743*100000000000000^3719 ≤ 50389399608459^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921280761 5000000000 50389399608459 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445000751/5000000000 : ℝ)^4743 ≤ (40157109976507/100000000000000 : ℝ)^3719 := by
    have hnat : (2445000751 : ℕ)^4743*100000000000000^3719 ≤ 40157109976507^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445000751 5000000000 40157109976507 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49159663/312500000 : ℝ), (2921280761/5000000000 : ℝ), (2445000751/5000000000 : ℝ)] ![(9453490402849/100000000000000 : ℝ), (50389399608459/100000000000000 : ℝ), (40157109976507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49159663/312500000 : ℝ)|^4743 ≤ (9453490402849/100000000000000 : ℝ)^3719
        have hw : |(-49159663/312500000 : ℝ)|=(49159663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2921280761/5000000000 : ℝ)|^4743 ≤ (50389399608459/100000000000000 : ℝ)^3719
        have hw : |(2921280761/5000000000 : ℝ)|=(2921280761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2445000751/5000000000 : ℝ)|^4743 ≤ (40157109976507/100000000000000 : ℝ)^3719
        have hw : |(2445000751/5000000000 : ℝ)|=(2445000751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1363842401/2500000000 : ℝ)*x 0 + (-131311787/625000000 : ℝ)*x 1 + (4890001337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363842401/2500000000 : ℝ)^4743 ≤ (23085038738423/50000000000000 : ℝ)^3719 := by
    have hnat : (1363842401 : ℕ)^4743*50000000000000^3719 ≤ 23085038738423^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363842401 2500000000 23085038738423 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131311787/625000000 : ℝ)^4743 ≤ (13672814254327/100000000000000 : ℝ)^3719 := by
    have hnat : (131311787 : ℕ)^4743*100000000000000^3719 ≤ 13672814254327^3719*625000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131311787 625000000 13672814254327 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4890001337/10000000000 : ℝ)^4743 ≤ (1606284329937/4000000000000 : ℝ)^3719 := by
    have hnat : (4890001337 : ℕ)^4743*4000000000000^3719 ≤ 1606284329937^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4890001337 10000000000 1606284329937 4000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1363842401/2500000000 : ℝ), (-131311787/625000000 : ℝ), (4890001337/10000000000 : ℝ)] ![(23085038738423/50000000000000 : ℝ), (13672814254327/100000000000000 : ℝ), (1606284329937/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1363842401/2500000000 : ℝ)|^4743 ≤ (23085038738423/50000000000000 : ℝ)^3719
        have hw : |(1363842401/2500000000 : ℝ)|=(1363842401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131311787/625000000 : ℝ)|^4743 ≤ (13672814254327/100000000000000 : ℝ)^3719
        have hw : |(-131311787/625000000 : ℝ)|=(131311787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4890001337/10000000000 : ℝ)|^4743 ≤ (1606284329937/4000000000000 : ℝ)^3719
        have hw : |(4890001337/10000000000 : ℝ)|=(4890001337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5455369469/10000000000 : ℝ)*x 0 + (244500071/500000000 : ℝ)*x 1 + (-262623583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5455369469/10000000000 : ℝ)^4743 ≤ (1154251900493/2500000000000 : ℝ)^3719 := by
    have hnat : (5455369469 : ℕ)^4743*2500000000000^3719 ≤ 1154251900493^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455369469 10000000000 1154251900493 2500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244500071/500000000 : ℝ)^4743 ≤ (40157109117703/100000000000000 : ℝ)^3719 := by
    have hnat : (244500071 : ℕ)^4743*100000000000000^3719 ≤ 40157109117703^3719*500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244500071 500000000 40157109117703 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262623583/1250000000 : ℝ)^4743 ≤ (213637732061/1562500000000 : ℝ)^3719 := by
    have hnat : (262623583 : ℕ)^4743*1562500000000^3719 ≤ 213637732061^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262623583 1250000000 213637732061 1562500000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5455369469/10000000000 : ℝ), (244500071/500000000 : ℝ), (-262623583/1250000000 : ℝ)] ![(1154251900493/2500000000000 : ℝ), (40157109117703/100000000000000 : ℝ), (213637732061/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5455369469/10000000000 : ℝ)|^4743 ≤ (1154251900493/2500000000000 : ℝ)^3719
        have hw : |(5455369469/10000000000 : ℝ)|=(5455369469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244500071/500000000 : ℝ)|^4743 ≤ (40157109117703/100000000000000 : ℝ)^3719
        have hw : |(244500071/500000000 : ℝ)|=(244500071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262623583/1250000000 : ℝ)|^4743 ≤ (213637732061/1562500000000 : ℝ)^3719
        have hw : |(-262623583/1250000000 : ℝ)|=(262623583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2055874151/5000000000 : ℝ)*x 0 + (3073657147/10000000000 : ℝ)*x 1 + (2701049463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055874151/5000000000 : ℝ)^4743 ≤ (1287690470377/4000000000000 : ℝ)^3719 := by
    have hnat : (2055874151 : ℕ)^4743*4000000000000^3719 ≤ 1287690470377^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055874151 5000000000 1287690470377 4000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3073657147/10000000000 : ℝ)^4743 ≤ (22211864432171/100000000000000 : ℝ)^3719 := by
    have hnat : (3073657147 : ℕ)^4743*100000000000000^3719 ≤ 22211864432171^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073657147 10000000000 22211864432171 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701049463/5000000000 : ℝ)^4743 ≤ (4559587378691/10000000000000 : ℝ)^3719 := by
    have hnat : (2701049463 : ℕ)^4743*10000000000000^3719 ≤ 4559587378691^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701049463 5000000000 4559587378691 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2055874151/5000000000 : ℝ), (3073657147/10000000000 : ℝ), (2701049463/5000000000 : ℝ)] ![(1287690470377/4000000000000 : ℝ), (22211864432171/100000000000000 : ℝ), (4559587378691/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2055874151/5000000000 : ℝ)|^4743 ≤ (1287690470377/4000000000000 : ℝ)^3719
        have hw : |(2055874151/5000000000 : ℝ)|=(2055874151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3073657147/10000000000 : ℝ)|^4743 ≤ (22211864432171/100000000000000 : ℝ)^3719
        have hw : |(3073657147/10000000000 : ℝ)|=(3073657147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701049463/5000000000 : ℝ)|^4743 ≤ (4559587378691/10000000000000 : ℝ)^3719
        have hw : |(2701049463/5000000000 : ℝ)|=(2701049463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1575957047/10000000000 : ℝ)*x 0 + (614269787/1250000000 : ℝ)*x 1 + (363596549/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1575957047/10000000000 : ℝ)^4743 ≤ (9475321856283/100000000000000 : ℝ)^3719 := by
    have hnat : (1575957047 : ℕ)^4743*100000000000000^3719 ≤ 9475321856283^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575957047 10000000000 9475321856283 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614269787/1250000000 : ℝ)^4743 ≤ (40410281358497/100000000000000 : ℝ)^3719 := by
    have hnat : (614269787 : ℕ)^4743*100000000000000^3719 ≤ 40410281358497^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614269787 1250000000 40410281358497 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (363596549/625000000 : ℝ)^4743 ≤ (10022879355323/20000000000000 : ℝ)^3719 := by
    have hnat : (363596549 : ℕ)^4743*20000000000000^3719 ≤ 10022879355323^3719*625000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363596549 625000000 10022879355323 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1575957047/10000000000 : ℝ), (614269787/1250000000 : ℝ), (363596549/625000000 : ℝ)] ![(9475321856283/100000000000000 : ℝ), (40410281358497/100000000000000 : ℝ), (10022879355323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1575957047/10000000000 : ℝ)|^4743 ≤ (9475321856283/100000000000000 : ℝ)^3719
        have hw : |(-1575957047/10000000000 : ℝ)|=(1575957047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614269787/1250000000 : ℝ)|^4743 ≤ (40410281358497/100000000000000 : ℝ)^3719
        have hw : |(614269787/1250000000 : ℝ)|=(614269787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(363596549/625000000 : ℝ)|^4743 ≤ (10022879355323/20000000000000 : ℝ)^3719
        have hw : |(363596549/625000000 : ℝ)|=(363596549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195203753/10000000000 : ℝ)*x 0 + (-293361073/2500000000 : ℝ)*x 1 + (2908772579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195203753/10000000000 : ℝ)^4743 ≤ (5422578000221/12500000000000 : ℝ)^3719 := by
    have hnat : (5195203753 : ℕ)^4743*12500000000000^3719 ≤ 5422578000221^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195203753 10000000000 5422578000221 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293361073/2500000000 : ℝ)^4743 ≤ (1626243772721/25000000000000 : ℝ)^3719 := by
    have hnat : (293361073 : ℕ)^4743*25000000000000^3719 ≤ 1626243772721^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293361073 2500000000 1626243772721 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2908772579/5000000000 : ℝ)^4743 ≤ (2004576035419/4000000000000 : ℝ)^3719 := by
    have hnat : (2908772579 : ℕ)^4743*4000000000000^3719 ≤ 2004576035419^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908772579 5000000000 2004576035419 4000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195203753/10000000000 : ℝ), (-293361073/2500000000 : ℝ), (2908772579/5000000000 : ℝ)] ![(5422578000221/12500000000000 : ℝ), (1626243772721/25000000000000 : ℝ), (2004576035419/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195203753/10000000000 : ℝ)|^4743 ≤ (5422578000221/12500000000000 : ℝ)^3719
        have hw : |(5195203753/10000000000 : ℝ)|=(5195203753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-293361073/2500000000 : ℝ)|^4743 ≤ (1626243772721/25000000000000 : ℝ)^3719
        have hw : |(-293361073/2500000000 : ℝ)|=(293361073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2908772579/5000000000 : ℝ)|^4743 ≤ (2004576035419/4000000000000 : ℝ)^3719
        have hw : |(2908772579/5000000000 : ℝ)|=(2908772579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195203923/10000000000 : ℝ)*x 0 + (1163508953/2000000000 : ℝ)*x 1 + (-146680581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195203923/10000000000 : ℝ)^4743 ≤ (8676125162429/20000000000000 : ℝ)^3719 := by
    have hnat : (5195203923 : ℕ)^4743*20000000000000^3719 ≤ 8676125162429^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195203923 10000000000 8676125162429 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163508953/2000000000 : ℝ)^4743 ≤ (50114396567877/100000000000000 : ℝ)^3719 := by
    have hnat : (1163508953 : ℕ)^4743*100000000000000^3719 ≤ 50114396567877^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163508953 2000000000 50114396567877 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146680581/1250000000 : ℝ)^4743 ≤ (26019910431/400000000000 : ℝ)^3719 := by
    have hnat : (146680581 : ℕ)^4743*400000000000^3719 ≤ 26019910431^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146680581 1250000000 26019910431 400000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195203923/10000000000 : ℝ), (1163508953/2000000000 : ℝ), (-146680581/1250000000 : ℝ)] ![(8676125162429/20000000000000 : ℝ), (50114396567877/100000000000000 : ℝ), (26019910431/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195203923/10000000000 : ℝ)|^4743 ≤ (8676125162429/20000000000000 : ℝ)^3719
        have hw : |(5195203923/10000000000 : ℝ)|=(5195203923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1163508953/2000000000 : ℝ)|^4743 ≤ (50114396567877/100000000000000 : ℝ)^3719
        have hw : |(1163508953/2000000000 : ℝ)|=(1163508953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-146680581/1250000000 : ℝ)|^4743 ≤ (26019910431/400000000000 : ℝ)^3719
        have hw : |(-146680581/1250000000 : ℝ)|=(146680581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s0_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (12870973/31250000 : ℝ)*x 0 + (5343051097/10000000000 : ℝ)*x 1 + (39185089/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12870973/31250000 : ℝ)^4743 ≤ (16130902356037/50000000000000 : ℝ)^3719 := by
    have hnat : (12870973 : ℕ)^4743*50000000000000^3719 ≤ 16130902356037^3719*31250000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12870973 31250000 16130902356037 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5343051097/10000000000 : ℝ)^4743 ≤ (8992243634519/20000000000000 : ℝ)^3719 := by
    have hnat : (5343051097 : ℕ)^4743*20000000000000^3719 ≤ 8992243634519^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343051097 10000000000 8992243634519 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39185089/125000000 : ℝ)^4743 ≤ (711780534331/3125000000000 : ℝ)^3719 := by
    have hnat : (39185089 : ℕ)^4743*3125000000000^3719 ≤ 711780534331^3719*125000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39185089 125000000 711780534331 3125000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(12870973/31250000 : ℝ), (5343051097/10000000000 : ℝ), (39185089/125000000 : ℝ)] ![(16130902356037/50000000000000 : ℝ), (8992243634519/20000000000000 : ℝ), (711780534331/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(12870973/31250000 : ℝ)|^4743 ≤ (16130902356037/50000000000000 : ℝ)^3719
        have hw : |(12870973/31250000 : ℝ)|=(12870973/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5343051097/10000000000 : ℝ)|^4743 ≤ (8992243634519/20000000000000 : ℝ)^3719
        have hw : |(5343051097/10000000000 : ℝ)|=(5343051097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39185089/125000000 : ℝ)|^4743 ≤ (711780534331/3125000000000 : ℝ)^3719
        have hw : |(39185089/125000000 : ℝ)|=(39185089/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (787/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4867/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4739/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4739 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4739*1^1024 ≤ 0^1024*1^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4739/1024 : ℝ) ≤ (1439997108452198567/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4739 ≤ (1439997108452198567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4739*100000000000000000000^1024 ≤ 1439997108452198567^1024*5^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1439997108452198567 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1439997108452198567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4739 := by
      have hnat : (1 : ℕ)^1024*1^4739 ≤ 1^4739*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101439997108452198567/100000000000000000000 : ℝ) ≤ (62693382685933/62500000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (101439997108452198567/100000000000000000000 : ℝ)^1024 ≤ (62693382685933/62500000000000 : ℝ)^4739 := by
      have hnat : (101439997108452198567 : ℕ)^1024*62500000000000^4739 ≤ 62693382685933^4739*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101439997108452198567 100000000000000000000 62693382685933 62500000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62693382685933/62500000000000 : ℝ)) (X := (101439997108452198567/100000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51439997108452198567/50000000000000000000 : ℝ) ≤ (31443382685933/31250000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (51439997108452198567/50000000000000000000 : ℝ)^1024 ≤ (31443382685933/31250000000000 : ℝ)^4739 := by
      have hnat : (51439997108452198567 : ℕ)^1024*31250000000000^4739 ≤ 31443382685933^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51439997108452198567 50000000000000000000 31443382685933 31250000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31443382685933/31250000000000 : ℝ)) (X := (51439997108452198567/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(193382685933/25000000000000 : ℝ)*(0 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(193382685933/25000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1439997108452198567/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(193382685933/25000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (1 : ℝ)+(193382685933/25000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(62693382685933/62500000000000 : ℝ) by norm_num, show 1+(1439997108452198567/100000000000000000000 : ℝ)+(0 : ℝ)=(101439997108452198567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1439997108452198567/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(193382685933/25000000000000 : ℝ)*(2/5 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(193382685933/25000000000000 : ℝ)*(2/5 : ℝ)=(31443382685933/31250000000000 : ℝ) by norm_num, show 1+2*(1439997108452198567/100000000000000000000 : ℝ)=(51439997108452198567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(193382685933/25000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (193382685933/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(193382685933/25000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (193382685933/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(193382685933/25000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (193382685933/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-49159663/312500000 : ℝ)*X 0 0+(2921280761/5000000000 : ℝ)*X 0 1+(2445000751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1363842401/2500000000 : ℝ)*X 1 0+(-131311787/625000000 : ℝ)*X 1 1+(4890001337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5455369469/10000000000 : ℝ)*X 2 0+(244500071/500000000 : ℝ)*X 2 1+(-262623583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2055874151/5000000000 : ℝ)*X 0 0+(3073657147/10000000000 : ℝ)*X 0 1+(2701049463/5000000000 : ℝ)*X 0 2+(2055874151/5000000000 : ℝ)*X 1 0+(3073657147/10000000000 : ℝ)*X 1 1+(2701049463/5000000000 : ℝ)*X 1 2+(2055874151/5000000000 : ℝ)*X 2 0+(3073657147/10000000000 : ℝ)*X 2 1+(2701049463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1575957047/10000000000 : ℝ)*X 0 0+(614269787/1250000000 : ℝ)*X 0 1+(363596549/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195203753/10000000000 : ℝ)*X 1 0+(-293361073/2500000000 : ℝ)*X 1 1+(2908772579/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5195203923/10000000000 : ℝ)*X 2 0+(1163508953/2000000000 : ℝ)*X 2 1+(-146680581/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((12870973/31250000 : ℝ)*X 0 0+(5343051097/10000000000 : ℝ)*X 0 1+(39185089/125000000 : ℝ)*X 0 2+(12870973/31250000 : ℝ)*X 1 0+(5343051097/10000000000 : ℝ)*X 1 1+(39185089/125000000 : ℝ)*X 1 2+(12870973/31250000 : ℝ)*X 2 0+(5343051097/10000000000 : ℝ)*X 2 1+(39185089/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (296591527396260202131/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (25764401/100000000000000 : ℝ)*(base1) + (936620049/100000000000000 : ℝ)*(base19) + (455320607/50000000000000 : ℝ)*(base23) + (69149989/50000000000000 : ℝ)*(upper3) + (109002453/100000000000000 : ℝ)*(upper5) + (73964214493829/10000000000000 : ℝ)*(major0) + (73964214493829/10000000000000 : ℝ)*(major1) + (73964214493829/10000000000000 : ℝ)*(major2) + (262451512094853/25000000000000 : ℝ)*(sp0) + (524904216192127/50000000000000 : ℝ)*(sp1) + (65613028647693/6250000000000 : ℝ)*(sp2) + (85894635117949/20000000000000 : ℝ)*(sp3) + (836597323/25000000000000 : ℝ)*(sp4) + (780667989/50000000000000 : ℝ)*(sp7) + (107368690672531/25000000000000 : ℝ)*(f.failure) + (1049809369004303/100000000000000 : ℝ)*(f.sum) + (20310311793/125000000000000000000000000 : ℝ)*base66 + (1771779388207/250000000000000000000000000 : ℝ)*base67 + (1259671861957/250000000000000000000000000 : ℝ)*base69 + (1245701485957/250000000000000000000000000 : ℝ)*base71 + (37167139427/7812500000000000000000000 : ℝ)*base73 + (216282599543/250000000000000000000000000 : ℝ)*base76 + (1377715271957/250000000000000000000000000 : ℝ)*base77 + (2456771022207/250000000000000000000000000 : ℝ)*base79 + (237118257707/125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (42477/500000000000000000000 : ℝ)*base90 + (42477/500000000000000000000 : ℝ)*base92 + (42477/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9714361043056825359/976562500000000000000000 : ℝ) := by norm_num
    linear_combination (2049392111/100000000000000 : ℝ)*(base19) + (529985479/25000000000000 : ℝ)*(base23) + (299387067/100000000000000 : ℝ)*(base32) + (48117271/12500000000000 : ℝ)*(upper3) + (48894843/50000000000000 : ℝ)*(upper5) + (155979227352677/20000000000000 : ℝ)*(major0) + (155979227352677/20000000000000 : ℝ)*(major1) + (155979227352677/20000000000000 : ℝ)*(major2) + (5537318099/100000000000000 : ℝ)*(sp1) + (6222813339/100000000000000 : ℝ)*(sp2) + (34591987952383/3125000000000 : ℝ)*(sp4) + (221387205553209/20000000000000 : ℝ)*(sp5) + (1106935271721001/100000000000000 : ℝ)*(sp6) + (5660600350999/1250000000000 : ℝ)*(sp7) + (452848327466987/100000000000000 : ℝ)*(f.failure) + (34591987952383/3125000000000 : ℝ)*(f.sum) + (80689000641/250000000000000000000000000 : ℝ)*base65 + (499228215359/500000000000000000000000000 : ℝ)*base68 + (174478240641/500000000000000000000000000 : ℝ)*base69 + (83442647859/500000000000000000000000000 : ℝ)*base72 + (222097669641/250000000000000000000000000 : ℝ)*base73 + (2091373356141/500000000000000000000000000 : ℝ)*base75 + (1118244764359/500000000000000000000000000 : ℝ)*base78 + (3947043899859/500000000000000000000000000 : ℝ)*base80 + (902970628641/250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6638571/2000000000000000000000 : ℝ)*base89 + (6638571/2000000000000000000000 : ℝ)*base91 + (6638571/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1606_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (787/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4867/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1606_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1606_s1_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-849188733/5000000000 : ℝ)*x 0 + (2766849777/5000000000 : ℝ)*x 1 + (2558941849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849188733/5000000000 : ℝ)^4743 ≤ (2084777226853/20000000000000 : ℝ)^3719 := by
    have hnat : (849188733 : ℕ)^4743*20000000000000^3719 ≤ 2084777226853^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849188733 5000000000 2084777226853 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2766849777/5000000000 : ℝ)^4743 ≤ (47017199361993/100000000000000 : ℝ)^3719 := by
    have hnat : (2766849777 : ℕ)^4743*100000000000000^3719 ≤ 47017199361993^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766849777 5000000000 47017199361993 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558941849/5000000000 : ℝ)^4743 ≤ (42558914480317/100000000000000 : ℝ)^3719 := by
    have hnat : (2558941849 : ℕ)^4743*100000000000000^3719 ≤ 42558914480317^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558941849 5000000000 42558914480317 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-849188733/5000000000 : ℝ), (2766849777/5000000000 : ℝ), (2558941849/5000000000 : ℝ)] ![(2084777226853/20000000000000 : ℝ), (47017199361993/100000000000000 : ℝ), (42558914480317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-849188733/5000000000 : ℝ)|^4743 ≤ (2084777226853/20000000000000 : ℝ)^3719
        have hw : |(-849188733/5000000000 : ℝ)|=(849188733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2766849777/5000000000 : ℝ)|^4743 ≤ (47017199361993/100000000000000 : ℝ)^3719
        have hw : |(2766849777/5000000000 : ℝ)|=(2766849777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2558941849/5000000000 : ℝ)|^4743 ≤ (42558914480317/100000000000000 : ℝ)^3719
        have hw : |(2558941849/5000000000 : ℝ)|=(2558941849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074633237/2000000000 : ℝ)*x 0 + (-1915992029/10000000000 : ℝ)*x 1 + (2558941779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074633237/2000000000 : ℝ)^4743 ≤ (22642330018369/50000000000000 : ℝ)^3719 := by
    have hnat : (1074633237 : ℕ)^4743*50000000000000^3719 ≤ 22642330018369^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074633237 2000000000 22642330018369 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915992029/10000000000 : ℝ)^4743 ≤ (94972085619/781250000000 : ℝ)^3719 := by
    have hnat : (1915992029 : ℕ)^4743*781250000000^3719 ≤ 94972085619^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915992029 10000000000 94972085619 781250000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558941779/5000000000 : ℝ)^4743 ≤ (42558912995561/100000000000000 : ℝ)^3719 := by
    have hnat : (2558941779 : ℕ)^4743*100000000000000^3719 ≤ 42558912995561^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558941779 5000000000 42558912995561 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074633237/2000000000 : ℝ), (-1915992029/10000000000 : ℝ), (2558941779/5000000000 : ℝ)] ![(22642330018369/50000000000000 : ℝ), (94972085619/781250000000 : ℝ), (42558912995561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074633237/2000000000 : ℝ)|^4743 ≤ (22642330018369/50000000000000 : ℝ)^3719
        have hw : |(1074633237/2000000000 : ℝ)|=(1074633237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1915992029/10000000000 : ℝ)|^4743 ≤ (94972085619/781250000000 : ℝ)^3719
        have hw : |(-1915992029/10000000000 : ℝ)|=(1915992029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2558941779/5000000000 : ℝ)|^4743 ≤ (42558912995561/100000000000000 : ℝ)^3719
        have hw : |(2558941779/5000000000 : ℝ)|=(2558941779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537316583/1000000000 : ℝ)*x 0 + (5117883859/10000000000 : ℝ)*x 1 + (-957996053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537316583/1000000000 : ℝ)^4743 ≤ (45284656221021/100000000000000 : ℝ)^3719 := by
    have hnat : (537316583 : ℕ)^4743*100000000000000^3719 ≤ 45284656221021^3719*1000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537316583 1000000000 45284656221021 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5117883859/10000000000 : ℝ)^4743 ≤ (42558916187787/100000000000000 : ℝ)^3719 := by
    have hnat : (5117883859 : ℕ)^4743*100000000000000^3719 ≤ 42558916187787^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117883859 10000000000 42558916187787 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957996053/5000000000 : ℝ)^4743 ≤ (3039106895573/25000000000000 : ℝ)^3719 := by
    have hnat : (957996053 : ℕ)^4743*25000000000000^3719 ≤ 3039106895573^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957996053 5000000000 3039106895573 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537316583/1000000000 : ℝ), (5117883859/10000000000 : ℝ), (-957996053/5000000000 : ℝ)] ![(45284656221021/100000000000000 : ℝ), (42558916187787/100000000000000 : ℝ), (3039106895573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537316583/1000000000 : ℝ)|^4743 ≤ (45284656221021/100000000000000 : ℝ)^3719
        have hw : |(537316583/1000000000 : ℝ)|=(537316583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5117883859/10000000000 : ℝ)|^4743 ≤ (42558916187787/100000000000000 : ℝ)^3719
        have hw : |(5117883859/10000000000 : ℝ)|=(5117883859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957996053/5000000000 : ℝ)|^4743 ≤ (3039106895573/25000000000000 : ℝ)^3719
        have hw : |(-957996053/5000000000 : ℝ)|=(957996053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102077591/5000000000 : ℝ)*x 0 + (3719671763/10000000000 : ℝ)*x 1 + (2368046787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102077591/5000000000 : ℝ)^4743 ≤ (33117792091147/100000000000000 : ℝ)^3719 := by
    have hnat : (2102077591 : ℕ)^4743*100000000000000^3719 ≤ 33117792091147^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102077591 5000000000 33117792091147 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3719671763/10000000000 : ℝ)^4743 ≤ (28329971795519/100000000000000 : ℝ)^3719 := by
    have hnat : (3719671763 : ℕ)^4743*100000000000000^3719 ≤ 28329971795519^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3719671763 10000000000 28329971795519 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2368046787/5000000000 : ℝ)^4743 ≤ (38552236092293/100000000000000 : ℝ)^3719 := by
    have hnat : (2368046787 : ℕ)^4743*100000000000000^3719 ≤ 38552236092293^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368046787 5000000000 38552236092293 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102077591/5000000000 : ℝ), (3719671763/10000000000 : ℝ), (2368046787/5000000000 : ℝ)] ![(33117792091147/100000000000000 : ℝ), (28329971795519/100000000000000 : ℝ), (38552236092293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102077591/5000000000 : ℝ)|^4743 ≤ (33117792091147/100000000000000 : ℝ)^3719
        have hw : |(2102077591/5000000000 : ℝ)|=(2102077591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3719671763/10000000000 : ℝ)|^4743 ≤ (28329971795519/100000000000000 : ℝ)^3719
        have hw : |(3719671763/10000000000 : ℝ)|=(3719671763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2368046787/5000000000 : ℝ)|^4743 ≤ (38552236092293/100000000000000 : ℝ)^3719
        have hw : |(2368046787/5000000000 : ℝ)|=(2368046787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-849304421/5000000000 : ℝ)*x 0 + (2561221819/5000000000 : ℝ)*x 1 + (221162737/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849304421/5000000000 : ℝ)^4743 ≤ (10425697260993/100000000000000 : ℝ)^3719 := by
    have hnat : (849304421 : ℕ)^4743*100000000000000^3719 ≤ 10425697260993^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849304421 5000000000 10425697260993 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2561221819/5000000000 : ℝ)^4743 ≤ (42607280401213/100000000000000 : ℝ)^3719 := by
    have hnat : (2561221819 : ℕ)^4743*100000000000000^3719 ≤ 42607280401213^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561221819 5000000000 42607280401213 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221162737/400000000 : ℝ)^4743 ≤ (11741755582927/25000000000000 : ℝ)^3719 := by
    have hnat : (221162737 : ℕ)^4743*25000000000000^3719 ≤ 11741755582927^3719*400000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221162737 400000000 11741755582927 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-849304421/5000000000 : ℝ), (2561221819/5000000000 : ℝ), (221162737/400000000 : ℝ)] ![(10425697260993/100000000000000 : ℝ), (42607280401213/100000000000000 : ℝ), (11741755582927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-849304421/5000000000 : ℝ)|^4743 ≤ (10425697260993/100000000000000 : ℝ)^3719
        have hw : |(-849304421/5000000000 : ℝ)|=(849304421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2561221819/5000000000 : ℝ)|^4743 ≤ (42607280401213/100000000000000 : ℝ)^3719
        have hw : |(2561221819/5000000000 : ℝ)|=(2561221819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221162737/400000000 : ℝ)|^4743 ≤ (11741755582927/25000000000000 : ℝ)^3719
        have hw : |(221162737/400000000 : ℝ)|=(221162737/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42100929/80000000 : ℝ)*x 0 + (-18810087/125000000 : ℝ)*x 1 + (2764534371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42100929/80000000 : ℝ)^4743 ≤ (44099795530967/100000000000000 : ℝ)^3719 := by
    have hnat : (42100929 : ℕ)^4743*100000000000000^3719 ≤ 44099795530967^3719*80000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42100929 80000000 44099795530967 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18810087/125000000 : ℝ)^4743 ≤ (8933178688919/100000000000000 : ℝ)^3719 := by
    have hnat : (18810087 : ℕ)^4743*100000000000000^3719 ≤ 8933178688919^3719*125000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18810087 125000000 8933178688919 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2764534371/5000000000 : ℝ)^4743 ≤ (46967025765921/100000000000000 : ℝ)^3719 := by
    have hnat : (2764534371 : ℕ)^4743*100000000000000^3719 ≤ 46967025765921^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764534371 5000000000 46967025765921 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42100929/80000000 : ℝ), (-18810087/125000000 : ℝ), (2764534371/5000000000 : ℝ)] ![(44099795530967/100000000000000 : ℝ), (8933178688919/100000000000000 : ℝ), (46967025765921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42100929/80000000 : ℝ)|^4743 ≤ (44099795530967/100000000000000 : ℝ)^3719
        have hw : |(42100929/80000000 : ℝ)|=(42100929/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18810087/125000000 : ℝ)|^4743 ≤ (8933178688919/100000000000000 : ℝ)^3719
        have hw : |(-18810087/125000000 : ℝ)|=(18810087/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2764534371/5000000000 : ℝ)|^4743 ≤ (46967025765921/100000000000000 : ℝ)^3719
        have hw : |(2764534371/5000000000 : ℝ)|=(2764534371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526261551/1000000000 : ℝ)*x 0 + (5529068973/10000000000 : ℝ)*x 1 + (-752403749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526261551/1000000000 : ℝ)^4743 ≤ (44099788958371/100000000000000 : ℝ)^3719 := by
    have hnat : (526261551 : ℕ)^4743*100000000000000^3719 ≤ 44099788958371^3719*1000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526261551 1000000000 44099788958371 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5529068973/10000000000 : ℝ)^4743 ≤ (9393405653691/20000000000000 : ℝ)^3719 := by
    have hnat : (5529068973 : ℕ)^4743*20000000000000^3719 ≤ 9393405653691^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529068973 10000000000 9393405653691 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752403749/5000000000 : ℝ)^4743 ≤ (8933182762107/100000000000000 : ℝ)^3719 := by
    have hnat : (752403749 : ℕ)^4743*100000000000000^3719 ≤ 8933182762107^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752403749 5000000000 8933182762107 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526261551/1000000000 : ℝ), (5529068973/10000000000 : ℝ), (-752403749/5000000000 : ℝ)] ![(44099788958371/100000000000000 : ℝ), (9393405653691/20000000000000 : ℝ), (8933182762107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526261551/1000000000 : ℝ)|^4743 ≤ (44099788958371/100000000000000 : ℝ)^3719
        have hw : |(526261551/1000000000 : ℝ)|=(526261551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5529068973/10000000000 : ℝ)|^4743 ≤ (9393405653691/20000000000000 : ℝ)^3719
        have hw : |(5529068973/10000000000 : ℝ)|=(5529068973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-752403749/5000000000 : ℝ)|^4743 ≤ (8933182762107/100000000000000 : ℝ)^3719
        have hw : |(-752403749/5000000000 : ℝ)|=(752403749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s1_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4204719717/10000000000 : ℝ)*x 0 + (4724948351/10000000000 : ℝ)*x 1 + (1865495519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204719717/10000000000 : ℝ)^4743 ≤ (16561731864447/50000000000000 : ℝ)^3719 := by
    have hnat : (4204719717 : ℕ)^4743*50000000000000^3719 ≤ 16561731864447^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204719717 10000000000 16561731864447 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4724948351/10000000000 : ℝ)^4743 ≤ (38436570495339/100000000000000 : ℝ)^3719 := by
    have hnat : (4724948351 : ℕ)^4743*100000000000000^3719 ≤ 38436570495339^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724948351 10000000000 38436570495339 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865495519/5000000000 : ℝ)^4743 ≤ (28439965760113/100000000000000 : ℝ)^3719 := by
    have hnat : (1865495519 : ℕ)^4743*100000000000000^3719 ≤ 28439965760113^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865495519 5000000000 28439965760113 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204719717/10000000000 : ℝ), (4724948351/10000000000 : ℝ), (1865495519/5000000000 : ℝ)] ![(16561731864447/50000000000000 : ℝ), (38436570495339/100000000000000 : ℝ), (28439965760113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204719717/10000000000 : ℝ)|^4743 ≤ (16561731864447/50000000000000 : ℝ)^3719
        have hw : |(4204719717/10000000000 : ℝ)|=(4204719717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4724948351/10000000000 : ℝ)|^4743 ≤ (38436570495339/100000000000000 : ℝ)^3719
        have hw : |(4724948351/10000000000 : ℝ)|=(4724948351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1865495519/5000000000 : ℝ)|^4743 ≤ (28439965760113/100000000000000 : ℝ)^3719
        have hw : |(1865495519/5000000000 : ℝ)|=(1865495519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4867/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (787/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4529/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4467/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4867/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (787/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4867/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (787/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4867/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (787/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4867/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (787/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4867/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (787/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4867/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (787/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (787/20000 : ℝ) ^ (4739/1024 : ℝ) ≤ (3930185485049/12500000000000000000 : ℝ) := by
    have hpowers : (787/20000 : ℝ)^4739 ≤ (3930185485049/12500000000000000000 : ℝ)^1024 := by
      have hnat : (787 : ℕ)^4739*12500000000000000000^1024 ≤ 3930185485049^1024*20000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        787 20000 3930185485049 12500000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (787/20000 : ℝ)) (X := (3930185485049/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4867/20000 : ℝ) ^ (4739/1024 : ℝ) ≤ (144384923166352831/100000000000000000000 : ℝ) := by
    have hpowers : (4867/20000 : ℝ)^4739 ≤ (144384923166352831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4867 : ℕ)^4739*100000000000000000000^1024 ≤ 144384923166352831^1024*20000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4867 20000 144384923166352831 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4867/20000 : ℝ)) (X := (144384923166352831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250003930185485049/6250000000000000000 : ℝ) ≤ (10000001358770693/10000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (6250003930185485049/6250000000000000000 : ℝ)^1024 ≤ (10000001358770693/10000000000000000 : ℝ)^4739 := by
      have hnat : (6250003930185485049 : ℕ)^1024*10000000000000000^4739 ≤ 10000001358770693^4739*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250003930185485049 6250000000000000000 10000001358770693 10000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001358770693/10000000000000000 : ℝ)) (X := (6250003930185485049/6250000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100144416364650233223/100000000000000000000 : ℝ) ≤ (5001559387209211/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (100144416364650233223/100000000000000000000 : ℝ)^1024 ≤ (5001559387209211/5000000000000000 : ℝ)^4739 := by
      have hnat : (100144416364650233223 : ℕ)^1024*5000000000000000^4739 ≤ 5001559387209211^4739*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100144416364650233223 100000000000000000000 5001559387209211 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001559387209211/5000000000000000 : ℝ)) (X := (100144416364650233223/100000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50144384923166352831/50000000000000000000 : ℝ) ≤ (10006236190066151/10000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50144384923166352831/50000000000000000000 : ℝ)^1024 ≤ (10006236190066151/10000000000000000 : ℝ)^4739 := by
      have hnat : (50144384923166352831 : ℕ)^1024*10000000000000000^4739 ≤ 10006236190066151^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50144384923166352831 50000000000000000000 10006236190066151 10000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006236190066151/10000000000000000 : ℝ)) (X := (50144384923166352831/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3930185485049/12500000000000000000 : ℝ) ≤ ((6799183121925816999/6800000000000000000 : ℝ)+2*(1039138549243/680000000000000 : ℝ)*(787/20000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (6799183121925816999/6800000000000000000 : ℝ)+2*(1039138549243/680000000000000 : ℝ)*(787/20000 : ℝ)=(10000001358770693/10000000000000000 : ℝ) by norm_num, show 1+2*(3930185485049/12500000000000000000 : ℝ)=(6250003930185485049/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(144384923166352831/100000000000000000000 : ℝ)+(3930185485049/12500000000000000000 : ℝ) ≤ ((6799183121925816999/6800000000000000000 : ℝ)+(1039138549243/680000000000000 : ℝ)*((4867/20000 : ℝ)+(787/20000 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (6799183121925816999/6800000000000000000 : ℝ)+(1039138549243/680000000000000 : ℝ)*((4867/20000 : ℝ)+(787/20000 : ℝ))=(5001559387209211/5000000000000000 : ℝ) by norm_num, show 1+(144384923166352831/100000000000000000000 : ℝ)+(3930185485049/12500000000000000000 : ℝ)=(100144416364650233223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(144384923166352831/100000000000000000000 : ℝ) ≤ ((6799183121925816999/6800000000000000000 : ℝ)+2*(1039138549243/680000000000000 : ℝ)*(4867/20000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (6799183121925816999/6800000000000000000 : ℝ)+2*(1039138549243/680000000000000 : ℝ)*(4867/20000 : ℝ)=(10006236190066151/10000000000000000 : ℝ) by norm_num, show 1+2*(144384923166352831/100000000000000000000 : ℝ)=(50144384923166352831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6799183121925816999/6800000000000000000 : ℝ)*(X 1 0+X 2 0)+(1039138549243/680000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (787/20000 : ℝ)) (hi := (4867/20000 : ℝ)) (c := (6799183121925816999/6800000000000000000 : ℝ)) (alpha := (1039138549243/680000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6799183121925816999/6800000000000000000 : ℝ)*(X 0 1+X 2 1)+(1039138549243/680000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (787/20000 : ℝ)) (hi := (4867/20000 : ℝ)) (c := (6799183121925816999/6800000000000000000 : ℝ)) (alpha := (1039138549243/680000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6799183121925816999/6800000000000000000 : ℝ)*(X 0 2+X 1 2)+(1039138549243/680000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (787/20000 : ℝ)) (hi := (4867/20000 : ℝ)) (c := (6799183121925816999/6800000000000000000 : ℝ)) (alpha := (1039138549243/680000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-849188733/5000000000 : ℝ)*X 0 0+(2766849777/5000000000 : ℝ)*X 0 1+(2558941849/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074633237/2000000000 : ℝ)*X 1 0+(-1915992029/10000000000 : ℝ)*X 1 1+(2558941779/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537316583/1000000000 : ℝ)*X 2 0+(5117883859/10000000000 : ℝ)*X 2 1+(-957996053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2102077591/5000000000 : ℝ)*X 0 0+(3719671763/10000000000 : ℝ)*X 0 1+(2368046787/5000000000 : ℝ)*X 0 2+(2102077591/5000000000 : ℝ)*X 1 0+(3719671763/10000000000 : ℝ)*X 1 1+(2368046787/5000000000 : ℝ)*X 1 2+(2102077591/5000000000 : ℝ)*X 2 0+(3719671763/10000000000 : ℝ)*X 2 1+(2368046787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-849304421/5000000000 : ℝ)*X 0 0+(2561221819/5000000000 : ℝ)*X 0 1+(221162737/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42100929/80000000 : ℝ)*X 1 0+(-18810087/125000000 : ℝ)*X 1 1+(2764534371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526261551/1000000000 : ℝ)*X 2 0+(5529068973/10000000000 : ℝ)*X 2 1+(-752403749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204719717/10000000000 : ℝ)*X 0 0+(4724948351/10000000000 : ℝ)*X 0 1+(1865495519/5000000000 : ℝ)*X 0 2+(4204719717/10000000000 : ℝ)*X 1 0+(4724948351/10000000000 : ℝ)*X 1 1+(1865495519/5000000000 : ℝ)*X 1 2+(4204719717/10000000000 : ℝ)*X 2 0+(4724948351/10000000000 : ℝ)*X 2 1+(1865495519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182306162673925571674491/34000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89015703/100000000000000 : ℝ)*(base1) + (1263404621/100000000000000 : ℝ)*(base19) + (1104513219/100000000000000 : ℝ)*(base23) + (39670733/25000000000000 : ℝ)*(upper3) + (17424637/20000000000000 : ℝ)*(upper5) + (1694391208919607/100000000000000 : ℝ)*(major0) + (1694391208919607/100000000000000 : ℝ)*(major1) + (1694391208919607/100000000000000 : ℝ)*(major2) + (1202460652116977/50000000000000 : ℝ)*(sp0) + (1202464583321241/50000000000000 : ℝ)*(sp1) + (601232331383471/25000000000000 : ℝ)*(sp2) + (983847455661793/100000000000000 : ℝ)*(sp3) + (2303707213/25000000000000 : ℝ)*(sp4) + (4264383079/100000000000000 : ℝ)*(sp7) + (39354072362423/4000000000000 : ℝ)*(f.failure) + (2404930430047103/100000000000000 : ℝ)*(f.sum) + (5229236993501/34000000000000000000000000000 : ℝ)*base65 + (6948130718260009393/680000000000000000000000000000000 : ℝ)*base67 + (220932683019990607/680000000000000000000000000000000 : ℝ)*base70 + (2490675417859990607/680000000000000000000000000000000 : ℝ)*base72 + (248486052167501/34000000000000000000000000000 : ℝ)*base73 + (5378710261460009393/680000000000000000000000000000000 : ℝ)*base75 + (960071951859990607/680000000000000000000000000000000 : ℝ)*base78 + (4409365498740009393/680000000000000000000000000000000 : ℝ)*base79 + (1499285387501/34000000000000000000000000000 : ℝ)*base81 + (171959/80000000000000000000 : ℝ)*base89 + (171959/80000000000000000000 : ℝ)*base91 + (171959/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (883780906261375291415579031/85000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2028592427/100000000000000 : ℝ)*(base19) + (1761824507/100000000000000 : ℝ)*(base23) + (23228821/100000000000000 : ℝ)*(upper2) + (353583161/100000000000000 : ℝ)*(upper3) + (157304173/100000000000000 : ℝ)*(upper5) + (866336426366323/50000000000000 : ℝ)*(major0) + (866336426366323/50000000000000 : ℝ)*(major1) + (866336426366323/50000000000000 : ℝ)*(major2) + (15354280751/100000000000000 : ℝ)*(sp1) + (889684403/6250000000000 : ℝ)*(sp2) + (614816308264213/25000000000000 : ℝ)*(sp4) + (98369914007347/4000000000000 : ℝ)*(sp5) + (1229624618140949/50000000000000 : ℝ)*(sp6) + (201216025165537/20000000000000 : ℝ)*(sp7) + (201216025165537/20000000000000 : ℝ)*(f.failure) + (614816308264213/25000000000000 : ℝ)*(f.sum) + (29681063593511/17000000000000000000000000000 : ℝ)*base66 + (1592445843670585323/340000000000000000000000000000000 : ℝ)*base68 + (678318915869414677/340000000000000000000000000000000 : ℝ)*base69 + (2689532154630585323/340000000000000000000000000000000 : ℝ)*base72 + (77626263808511/17000000000000000000000000000 : ℝ)*base74 + (2802220558850585323/340000000000000000000000000000000 : ℝ)*base76 + (3215670428030585323/340000000000000000000000000000000 : ℝ)*base78 + (1856850927070585323/340000000000000000000000000000000 : ℝ)*base80 + (53993402597489/17000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2890721/400000000000000000000 : ℝ)*base89 + (2890721/400000000000000000000 : ℝ)*base91 + (2890721/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1606_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4867/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (787/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4467/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1606_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1606_s2_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1712842833/10000000000 : ℝ)*x 0 + (5468475287/10000000000 : ℝ)*x 1 + (2586822639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1712842833/10000000000 : ℝ)^4743 ≤ (10537246109557/100000000000000 : ℝ)^3719 := by
    have hnat : (1712842833 : ℕ)^4743*100000000000000^3719 ≤ 10537246109557^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712842833 10000000000 10537246109557 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468475287/10000000000 : ℝ)^4743 ≤ (23155790386797/50000000000000 : ℝ)^3719 := by
    have hnat : (5468475287 : ℕ)^4743*50000000000000^3719 ≤ 23155790386797^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468475287 10000000000 23155790386797 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586822639/5000000000 : ℝ)^4743 ≤ (43151173103193/100000000000000 : ℝ)^3719 := by
    have hnat : (2586822639 : ℕ)^4743*100000000000000^3719 ≤ 43151173103193^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586822639 5000000000 43151173103193 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1712842833/10000000000 : ℝ), (5468475287/10000000000 : ℝ), (2586822639/5000000000 : ℝ)] ![(10537246109557/100000000000000 : ℝ), (23155790386797/50000000000000 : ℝ), (43151173103193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1712842833/10000000000 : ℝ)|^4743 ≤ (10537246109557/100000000000000 : ℝ)^3719
        have hw : |(-1712842833/10000000000 : ℝ)|=(1712842833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468475287/10000000000 : ℝ)|^4743 ≤ (23155790386797/50000000000000 : ℝ)^3719
        have hw : |(5468475287/10000000000 : ℝ)|=(5468475287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586822639/5000000000 : ℝ)|^4743 ≤ (43151173103193/100000000000000 : ℝ)^3719
        have hw : |(2586822639/5000000000 : ℝ)|=(2586822639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678099867/5000000000 : ℝ)*x 0 + (-932569453/5000000000 : ℝ)*x 1 + (2586822581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678099867/5000000000 : ℝ)^4743 ≤ (4510237550679/10000000000000 : ℝ)^3719 := by
    have hnat : (2678099867 : ℕ)^4743*10000000000000^3719 ≤ 4510237550679^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678099867 5000000000 4510237550679 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932569453/5000000000 : ℝ)^4743 ≤ (11746452617619/100000000000000 : ℝ)^3719 := by
    have hnat : (932569453 : ℕ)^4743*100000000000000^3719 ≤ 11746452617619^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932569453 5000000000 11746452617619 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586822581/5000000000 : ℝ)^4743 ≤ (4315117186929/10000000000000 : ℝ)^3719 := by
    have hnat : (2586822581 : ℕ)^4743*10000000000000^3719 ≤ 4315117186929^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586822581 5000000000 4315117186929 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678099867/5000000000 : ℝ), (-932569453/5000000000 : ℝ), (2586822581/5000000000 : ℝ)] ![(4510237550679/10000000000000 : ℝ), (11746452617619/100000000000000 : ℝ), (4315117186929/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678099867/5000000000 : ℝ)|^4743 ≤ (4510237550679/10000000000000 : ℝ)^3719
        have hw : |(2678099867/5000000000 : ℝ)|=(2678099867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-932569453/5000000000 : ℝ)|^4743 ≤ (11746452617619/100000000000000 : ℝ)^3719
        have hw : |(-932569453/5000000000 : ℝ)|=(932569453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586822581/5000000000 : ℝ)|^4743 ≤ (4315117186929/10000000000000 : ℝ)^3719
        have hw : |(2586822581/5000000000 : ℝ)|=(2586822581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356199599/10000000000 : ℝ)*x 0 + (1293411329/2500000000 : ℝ)*x 1 + (-932569441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356199599/10000000000 : ℝ)^4743 ≤ (22551187028503/50000000000000 : ℝ)^3719 := by
    have hnat : (5356199599 : ℕ)^4743*50000000000000^3719 ≤ 22551187028503^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356199599 10000000000 22551187028503 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293411329/2500000000 : ℝ)^4743 ≤ (21575586753701/50000000000000 : ℝ)^3719 := by
    have hnat : (1293411329 : ℕ)^4743*50000000000000^3719 ≤ 21575586753701^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293411329 2500000000 21575586753701 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932569441/5000000000 : ℝ)^4743 ≤ (2936613106213/25000000000000 : ℝ)^3719 := by
    have hnat : (932569441 : ℕ)^4743*25000000000000^3719 ≤ 2936613106213^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932569441 5000000000 2936613106213 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356199599/10000000000 : ℝ), (1293411329/2500000000 : ℝ), (-932569441/5000000000 : ℝ)] ![(22551187028503/50000000000000 : ℝ), (21575586753701/50000000000000 : ℝ), (2936613106213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356199599/10000000000 : ℝ)|^4743 ≤ (22551187028503/50000000000000 : ℝ)^3719
        have hw : |(5356199599/10000000000 : ℝ)|=(5356199599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293411329/2500000000 : ℝ)|^4743 ≤ (21575586753701/50000000000000 : ℝ)^3719
        have hw : |(1293411329/2500000000 : ℝ)|=(1293411329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-932569441/5000000000 : ℝ)|^4743 ≤ (2936613106213/25000000000000 : ℝ)^3719
        have hw : |(-932569441/5000000000 : ℝ)|=(932569441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214817307/10000000000 : ℝ)*x 0 + (60412611/156250000 : ℝ)*x 1 + (4587090403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214817307/10000000000 : ℝ)^4743 ≤ (16612472611231/50000000000000 : ℝ)^3719 := by
    have hnat : (4214817307 : ℕ)^4743*50000000000000^3719 ≤ 16612472611231^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214817307 10000000000 16612472611231 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60412611/156250000 : ℝ)^4743 ≤ (2976292977057/10000000000000 : ℝ)^3719 := by
    have hnat : (60412611 : ℕ)^4743*10000000000000^3719 ≤ 2976292977057^3719*156250000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60412611 156250000 2976292977057 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4587090403/10000000000 : ℝ)^4743 ≤ (37012124990653/100000000000000 : ℝ)^3719 := by
    have hnat : (4587090403 : ℕ)^4743*100000000000000^3719 ≤ 37012124990653^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587090403 10000000000 37012124990653 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214817307/10000000000 : ℝ), (60412611/156250000 : ℝ), (4587090403/10000000000 : ℝ)] ![(16612472611231/50000000000000 : ℝ), (2976292977057/10000000000000 : ℝ), (37012124990653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214817307/10000000000 : ℝ)|^4743 ≤ (16612472611231/50000000000000 : ℝ)^3719
        have hw : |(4214817307/10000000000 : ℝ)|=(4214817307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60412611/156250000 : ℝ)|^4743 ≤ (2976292977057/10000000000000 : ℝ)^3719
        have hw : |(60412611/156250000 : ℝ)|=(60412611/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4587090403/10000000000 : ℝ)|^4743 ≤ (37012124990653/100000000000000 : ℝ)^3719
        have hw : |(4587090403/10000000000 : ℝ)|=(4587090403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1712925151/10000000000 : ℝ)*x 0 + (1035189031/2000000000 : ℝ)*x 1 + (683268771/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1712925151/10000000000 : ℝ)^4743 ≤ (10537891963387/100000000000000 : ℝ)^3719 := by
    have hnat : (1712925151 : ℕ)^4743*100000000000000^3719 ≤ 10537891963387^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712925151 10000000000 10537891963387 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035189031/2000000000 : ℝ)^4743 ≤ (21587819301423/50000000000000 : ℝ)^3719 := by
    have hnat : (1035189031 : ℕ)^4743*50000000000000^3719 ≤ 21587819301423^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035189031 2000000000 21587819301423 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683268771/1250000000 : ℝ)^4743 ≤ (46286469423807/100000000000000 : ℝ)^3719 := by
    have hnat : (683268771 : ℕ)^4743*100000000000000^3719 ≤ 46286469423807^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683268771 1250000000 46286469423807 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1712925151/10000000000 : ℝ), (1035189031/2000000000 : ℝ), (683268771/1250000000 : ℝ)] ![(10537891963387/100000000000000 : ℝ), (21587819301423/50000000000000 : ℝ), (46286469423807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1712925151/10000000000 : ℝ)|^4743 ≤ (10537891963387/100000000000000 : ℝ)^3719
        have hw : |(-1712925151/10000000000 : ℝ)|=(1712925151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035189031/2000000000 : ℝ)|^4743 ≤ (21587819301423/50000000000000 : ℝ)^3719
        have hw : |(1035189031/2000000000 : ℝ)|=(1035189031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683268771/1250000000 : ℝ)|^4743 ≤ (46286469423807/100000000000000 : ℝ)^3719
        have hw : |(683268771/1250000000 : ℝ)|=(683268771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82467887/156250000 : ℝ)*x 0 + (-1572634011/10000000000 : ℝ)*x 1 + (2733075147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82467887/156250000 : ℝ)^4743 ≤ (22131840327701/50000000000000 : ℝ)^3719 := by
    have hnat : (82467887 : ℕ)^4743*50000000000000^3719 ≤ 22131840327701^3719*156250000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82467887 156250000 22131840327701 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1572634011/10000000000 : ℝ)^4743 ≤ (1889969708653/20000000000000 : ℝ)^3719 := by
    have hnat : (1572634011 : ℕ)^4743*20000000000000^3719 ≤ 1889969708653^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572634011 10000000000 1889969708653 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733075147/5000000000 : ℝ)^4743 ≤ (4628647078453/10000000000000 : ℝ)^3719 := by
    have hnat : (2733075147 : ℕ)^4743*10000000000000^3719 ≤ 4628647078453^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733075147 5000000000 4628647078453 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82467887/156250000 : ℝ), (-1572634011/10000000000 : ℝ), (2733075147/5000000000 : ℝ)] ![(22131840327701/50000000000000 : ℝ), (1889969708653/20000000000000 : ℝ), (4628647078453/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82467887/156250000 : ℝ)|^4743 ≤ (22131840327701/50000000000000 : ℝ)^3719
        have hw : |(82467887/156250000 : ℝ)|=(82467887/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1572634011/10000000000 : ℝ)|^4743 ≤ (1889969708653/20000000000000 : ℝ)^3719
        have hw : |(-1572634011/10000000000 : ℝ)|=(1572634011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733075147/5000000000 : ℝ)|^4743 ≤ (4628647078453/10000000000000 : ℝ)^3719
        have hw : |(2733075147/5000000000 : ℝ)|=(2733075147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277945049/10000000000 : ℝ)*x 0 + (1093229959/2000000000 : ℝ)*x 1 + (-1572634323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277945049/10000000000 : ℝ)^4743 ≤ (44263683660897/100000000000000 : ℝ)^3719 := by
    have hnat : (5277945049 : ℕ)^4743*100000000000000^3719 ≤ 44263683660897^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277945049 10000000000 44263683660897 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093229959/2000000000 : ℝ)^4743 ≤ (2892904087227/6250000000000 : ℝ)^3719 := by
    have hnat : (1093229959 : ℕ)^4743*6250000000000^3719 ≤ 2892904087227^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093229959 2000000000 2892904087227 6250000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572634323/10000000000 : ℝ)^4743 ≤ (472492546713/5000000000000 : ℝ)^3719 := by
    have hnat : (1572634323 : ℕ)^4743*5000000000000^3719 ≤ 472492546713^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572634323 10000000000 472492546713 5000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277945049/10000000000 : ℝ), (1093229959/2000000000 : ℝ), (-1572634323/10000000000 : ℝ)] ![(44263683660897/100000000000000 : ℝ), (2892904087227/6250000000000 : ℝ), (472492546713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277945049/10000000000 : ℝ)|^4743 ≤ (44263683660897/100000000000000 : ℝ)^3719
        have hw : |(5277945049/10000000000 : ℝ)|=(5277945049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093229959/2000000000 : ℝ)|^4743 ≤ (2892904087227/6250000000000 : ℝ)^3719
        have hw : |(1093229959/2000000000 : ℝ)|=(1093229959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1572634323/10000000000 : ℝ)|^4743 ≤ (472492546713/5000000000000 : ℝ)^3719
        have hw : |(-1572634323/10000000000 : ℝ)|=(1572634323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s2_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210750953/500000000 : ℝ)*x 0 + (4581468797/10000000000 : ℝ)*x 1 + (3872090847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210750953/500000000 : ℝ)^4743 ≤ (8306743384279/25000000000000 : ℝ)^3719 := by
    have hnat : (210750953 : ℕ)^4743*25000000000000^3719 ≤ 8306743384279^3719*500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210750953 500000000 8306743384279 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581468797/10000000000 : ℝ)^4743 ≤ (36954285991541/100000000000000 : ℝ)^3719 := by
    have hnat : (4581468797 : ℕ)^4743*100000000000000^3719 ≤ 36954285991541^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581468797 10000000000 36954285991541 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3872090847/10000000000 : ℝ)^4743 ≤ (29818740452777/100000000000000 : ℝ)^3719 := by
    have hnat : (3872090847 : ℕ)^4743*100000000000000^3719 ≤ 29818740452777^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872090847 10000000000 29818740452777 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210750953/500000000 : ℝ), (4581468797/10000000000 : ℝ), (3872090847/10000000000 : ℝ)] ![(8306743384279/25000000000000 : ℝ), (36954285991541/100000000000000 : ℝ), (29818740452777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210750953/500000000 : ℝ)|^4743 ≤ (8306743384279/25000000000000 : ℝ)^3719
        have hw : |(210750953/500000000 : ℝ)|=(210750953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4581468797/10000000000 : ℝ)|^4743 ≤ (36954285991541/100000000000000 : ℝ)^3719
        have hw : |(4581468797/10000000000 : ℝ)|=(4581468797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3872090847/10000000000 : ℝ)|^4743 ≤ (29818740452777/100000000000000 : ℝ)^3719
        have hw : |(3872090847/10000000000 : ℝ)|=(3872090847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4467/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5131/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16511/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4467/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4467/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4467/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4467/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4467/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4467/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4529/50000 : ℝ) ^ (4739/1024 : ℝ) ≤ (298022387359197/20000000000000000000 : ℝ) := by
    have hpowers : (4529/50000 : ℝ)^4739 ≤ (298022387359197/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4529 : ℕ)^4739*20000000000000000000^1024 ≤ 298022387359197^1024*50000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4529 50000 298022387359197 20000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4529/50000 : ℝ)) (X := (298022387359197/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4467/25000 : ℝ) ^ (4739/1024 : ℝ) ≤ (6913373999687879/20000000000000000000 : ℝ) := by
    have hpowers : (4467/25000 : ℝ)^4739 ≤ (6913373999687879/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4467 : ℕ)^4739*20000000000000000000^1024 ≤ 6913373999687879^1024*25000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4467 25000 6913373999687879 20000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4467/25000 : ℝ)) (X := (6913373999687879/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000298022387359197/10000000000000000000 : ℝ) ≤ (1250008049466129/1250000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (10000298022387359197/10000000000000000000 : ℝ)^1024 ≤ (1250008049466129/1250000000000000 : ℝ)^4739 := by
      have hnat : (10000298022387359197 : ℕ)^1024*1250000000000000^4739 ≤ 1250008049466129^4739*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000298022387359197 10000000000000000000 1250008049466129 1250000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250008049466129/1250000000000000 : ℝ)) (X := (10000298022387359197/10000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001802849096761769/5000000000000000000 : ℝ) ≤ (5000389503401763/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (5001802849096761769/5000000000000000000 : ℝ)^1024 ≤ (5000389503401763/5000000000000000 : ℝ)^4739 := by
      have hnat : (5001802849096761769 : ℕ)^1024*5000000000000000^4739 ≤ 5000389503401763^4739*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001802849096761769 5000000000000000000 5000389503401763 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000389503401763/5000000000000000 : ℝ)) (X := (5001802849096761769/5000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006913373999687879/10000000000000000000 : ℝ) ≤ (500074680893901/500000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (10006913373999687879/10000000000000000000 : ℝ)^1024 ≤ (500074680893901/500000000000000 : ℝ)^4739 := by
      have hnat : (10006913373999687879 : ℕ)^1024*500000000000000^4739 ≤ 500074680893901^4739*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006913373999687879 10000000000000000000 500074680893901 500000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500074680893901/500000000000000 : ℝ)) (X := (10006913373999687879/10000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(298022387359197/20000000000000000000 : ℝ) ≤ ((11010952679018404827/11012500000000000000 : ℝ)+2*(357305537247/440500000000000 : ℝ)*(4529/50000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (11010952679018404827/11012500000000000000 : ℝ)+2*(357305537247/440500000000000 : ℝ)*(4529/50000 : ℝ)=(1250008049466129/1250000000000000 : ℝ) by norm_num, show 1+2*(298022387359197/20000000000000000000 : ℝ)=(10000298022387359197/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6913373999687879/20000000000000000000 : ℝ)+(298022387359197/20000000000000000000 : ℝ) ≤ ((11010952679018404827/11012500000000000000 : ℝ)+(357305537247/440500000000000 : ℝ)*((4467/25000 : ℝ)+(4529/50000 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (11010952679018404827/11012500000000000000 : ℝ)+(357305537247/440500000000000 : ℝ)*((4467/25000 : ℝ)+(4529/50000 : ℝ))=(5000389503401763/5000000000000000 : ℝ) by norm_num, show 1+(6913373999687879/20000000000000000000 : ℝ)+(298022387359197/20000000000000000000 : ℝ)=(5001802849096761769/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6913373999687879/20000000000000000000 : ℝ) ≤ ((11010952679018404827/11012500000000000000 : ℝ)+2*(357305537247/440500000000000 : ℝ)*(4467/25000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (11010952679018404827/11012500000000000000 : ℝ)+2*(357305537247/440500000000000 : ℝ)*(4467/25000 : ℝ)=(500074680893901/500000000000000 : ℝ) by norm_num, show 1+2*(6913373999687879/20000000000000000000 : ℝ)=(10006913373999687879/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11010952679018404827/11012500000000000000 : ℝ)*(X 1 0+X 2 0)+(357305537247/440500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (4529/50000 : ℝ)) (hi := (4467/25000 : ℝ)) (c := (11010952679018404827/11012500000000000000 : ℝ)) (alpha := (357305537247/440500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11010952679018404827/11012500000000000000 : ℝ)*(X 0 1+X 2 1)+(357305537247/440500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (4529/50000 : ℝ)) (hi := (4467/25000 : ℝ)) (c := (11010952679018404827/11012500000000000000 : ℝ)) (alpha := (357305537247/440500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11010952679018404827/11012500000000000000 : ℝ)*(X 0 2+X 1 2)+(357305537247/440500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (4529/50000 : ℝ)) (hi := (4467/25000 : ℝ)) (c := (11010952679018404827/11012500000000000000 : ℝ)) (alpha := (357305537247/440500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1712842833/10000000000 : ℝ)*X 0 0+(5468475287/10000000000 : ℝ)*X 0 1+(2586822639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678099867/5000000000 : ℝ)*X 1 0+(-932569453/5000000000 : ℝ)*X 1 1+(2586822581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356199599/10000000000 : ℝ)*X 2 0+(1293411329/2500000000 : ℝ)*X 2 1+(-932569441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4214817307/10000000000 : ℝ)*X 0 0+(60412611/156250000 : ℝ)*X 0 1+(4587090403/10000000000 : ℝ)*X 0 2+(4214817307/10000000000 : ℝ)*X 1 0+(60412611/156250000 : ℝ)*X 1 1+(4587090403/10000000000 : ℝ)*X 1 2+(4214817307/10000000000 : ℝ)*X 2 0+(60412611/156250000 : ℝ)*X 2 1+(4587090403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1712925151/10000000000 : ℝ)*X 0 0+(1035189031/2000000000 : ℝ)*X 0 1+(683268771/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82467887/156250000 : ℝ)*X 1 0+(-1572634011/10000000000 : ℝ)*X 1 1+(2733075147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277945049/10000000000 : ℝ)*X 2 0+(1093229959/2000000000 : ℝ)*X 2 1+(-1572634323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((210750953/500000000 : ℝ)*X 0 0+(4581468797/10000000000 : ℝ)*X 0 1+(3872090847/10000000000 : ℝ)*X 0 2+(210750953/500000000 : ℝ)*X 1 0+(4581468797/10000000000 : ℝ)*X 1 1+(3872090847/10000000000 : ℝ)*X 1 2+(210750953/500000000 : ℝ)*X 2 0+(4581468797/10000000000 : ℝ)*X 2 1+(3872090847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (649415985503225193648130251/68828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (855584449/50000000000000 : ℝ)*(base19) + (784777839/50000000000000 : ℝ)*(base23) + (30061271/100000000000000 : ℝ)*(lower2) + (45645373/20000000000000 : ℝ)*(upper3) + (189675489/100000000000000 : ℝ)*(upper5) + (597426454821671/25000000000000 : ℝ)*(major0) + (597426454821671/25000000000000 : ℝ)*(major1) + (597426454821671/25000000000000 : ℝ)*(major2) + (423975567675961/12500000000000 : ℝ)*(sp0) + (423977739632317/12500000000000 : ℝ)*(sp1) + (847955514667939/25000000000000 : ℝ)*(sp2) + (1387579667454841/100000000000000 : ℝ)*(sp3) + (9543409873/50000000000000 : ℝ)*(sp4) + (802838013/10000000000000 : ℝ)*(sp7) + (1387587695834971/100000000000000 : ℝ)*(f.failure) + (1695911814113717/50000000000000 : ℝ)*(f.sum) + (64836067075977/22025000000000000000000000000 : ℝ)*base66 + (1020346171573469083/275312500000000000000000000000000 : ℝ)*base68 + (1477680007093781583/275312500000000000000000000000000 : ℝ)*base70 + (1427976405989406583/275312500000000000000000000000000 : ℝ)*base72 + (17045830384251/11012500000000000000000000000 : ℝ)*base74 + (1724345261831218417/275312500000000000000000000000000 : ℝ)*base75 + (2356934857870656583/275312500000000000000000000000000 : ℝ)*base78 + (724125837389094083/275312500000000000000000000000000 : ℝ)*base80 + (88877786289077/22025000000000000000000000000 : ℝ)*base82 + (23678043/2000000000000000000000 : ℝ)*base89 + (23678043/2000000000000000000000 : ℝ)*base91 + (23678043/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1927467925785927230448819741/275312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405798727/50000000000000 : ℝ)*(base19) + (571103151/50000000000000 : ℝ)*(base23) + (106671423/100000000000000 : ℝ)*(upper3) + (91143523/100000000000000 : ℝ)*(lower4) + (6242379/5000000000000 : ℝ)*(upper5) + (1213881294488039/50000000000000 : ℝ)*(major0) + (1213881294488039/50000000000000 : ℝ)*(major1) + (1213881294488039/50000000000000 : ℝ)*(major2) + (2604332439/25000000000000 : ℝ)*(sp1) + (869504991/10000000000000 : ℝ)*(sp2) + (1722919752807151/50000000000000 : ℝ)*(sp4) + (3445828276687093/100000000000000 : ℝ)*(sp5) + (344582966835809/10000000000000 : ℝ)*(sp6) + (1409685438970563/100000000000000 : ℝ)*(sp7) + (1409685438970563/100000000000000 : ℝ)*(f.failure) + (1722919752807151/50000000000000 : ℝ)*(f.sum) + (7235223066477/2753125000000000000000000000 : ℝ)*base65 + (1554405826626564253/550625000000000000000000000000000 : ℝ)*base67 + (1664855653529064253/550625000000000000000000000000000 : ℝ)*base69 + (745721837784689253/550625000000000000000000000000000 : ℝ)*base71 + (22778357019733/11012500000000000000000000000 : ℝ)*base73 + (7153675222544685747/550625000000000000000000000000000 : ℝ)*base76 + (2203987081827189253/550625000000000000000000000000000 : ℝ)*base77 + (3490534017310935747/550625000000000000000000000000000 : ℝ)*base80 + (48816470885991/22025000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1999421/2000000000000000000000 : ℝ)*base90 + (1999421/2000000000000000000000 : ℝ)*base92 + (1999421/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1606_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4467/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1606_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1606_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1606_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1606_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1606_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1606_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
