-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1546_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:20.356587+00:00
-- url     : https://prove2.me/submissions/f703dbee-b6cc-403d-a01b-e2c310349d1d

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
theorem support_rectangle_w1546_s6_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818934417/10000000000 : ℝ)*x 0 + (339302703/625000000 : ℝ)*x 1 + (326198587/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818934417/10000000000 : ℝ)^4589 ≤ (5574155660983/50000000000000 : ℝ)^3565 := by
    have hnat : (1818934417 : ℕ)^4589*50000000000000^3565 ≤ 5574155660983^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818934417 10000000000 5574155660983 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339302703/625000000 : ℝ)^4589 ≤ (45551786711893/100000000000000 : ℝ)^3565 := by
    have hnat : (339302703 : ℕ)^4589*100000000000000^3565 ≤ 45551786711893^3565*625000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339302703 625000000 45551786711893 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326198587/625000000 : ℝ)^4589 ≤ (43299901954617/100000000000000 : ℝ)^3565 := by
    have hnat : (326198587 : ℕ)^4589*100000000000000^3565 ≤ 43299901954617^3565*625000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326198587 625000000 43299901954617 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818934417/10000000000 : ℝ), (339302703/625000000 : ℝ), (326198587/625000000 : ℝ)] ![(5574155660983/50000000000000 : ℝ), (45551786711893/100000000000000 : ℝ), (43299901954617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818934417/10000000000 : ℝ)|^4589 ≤ (5574155660983/50000000000000 : ℝ)^3565
        have hw : |(-1818934417/10000000000 : ℝ)|=(1818934417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339302703/625000000 : ℝ)|^4589 ≤ (45551786711893/100000000000000 : ℝ)^3565
        have hw : |(339302703/625000000 : ℝ)|=(339302703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326198587/625000000 : ℝ)|^4589 ≤ (43299901954617/100000000000000 : ℝ)^3565
        have hw : |(326198587/625000000 : ℝ)|=(326198587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s6_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069927381/2000000000 : ℝ)*x 0 + (-963121863/5000000000 : ℝ)*x 1 + (260958871/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069927381/2000000000 : ℝ)^4589 ≤ (11174523068639/25000000000000 : ℝ)^3565 := by
    have hnat : (1069927381 : ℕ)^4589*25000000000000^3565 ≤ 11174523068639^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069927381 2000000000 11174523068639 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963121863/5000000000 : ℝ)^4589 ≤ (600100272659/5000000000000 : ℝ)^3565 := by
    have hnat : (963121863 : ℕ)^4589*5000000000000^3565 ≤ 600100272659^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963121863 5000000000 600100272659 5000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260958871/500000000 : ℝ)^4589 ≤ (21649951126819/50000000000000 : ℝ)^3565 := by
    have hnat : (260958871 : ℕ)^4589*50000000000000^3565 ≤ 21649951126819^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260958871 500000000 21649951126819 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069927381/2000000000 : ℝ), (-963121863/5000000000 : ℝ), (260958871/500000000 : ℝ)] ![(11174523068639/25000000000000 : ℝ), (600100272659/5000000000000 : ℝ), (21649951126819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069927381/2000000000 : ℝ)|^4589 ≤ (11174523068639/25000000000000 : ℝ)^3565
        have hw : |(1069927381/2000000000 : ℝ)|=(1069927381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-963121863/5000000000 : ℝ)|^4589 ≤ (600100272659/5000000000000 : ℝ)^3565
        have hw : |(-963121863/5000000000 : ℝ)|=(963121863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260958871/500000000 : ℝ)|^4589 ≤ (21649951126819/50000000000000 : ℝ)^3565
        have hw : |(260958871/500000000 : ℝ)|=(260958871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s6_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349636903/10000000000 : ℝ)*x 0 + (5219177403/10000000000 : ℝ)*x 1 + (-240780469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349636903/10000000000 : ℝ)^4589 ≤ (8939618450609/20000000000000 : ℝ)^3565 := by
    have hnat : (5349636903 : ℕ)^4589*20000000000000^3565 ≤ 8939618450609^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349636903 10000000000 8939618450609 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219177403/10000000000 : ℝ)^4589 ≤ (43299902072089/100000000000000 : ℝ)^3565 := by
    have hnat : (5219177403 : ℕ)^4589*100000000000000^3565 ≤ 43299902072089^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219177403 10000000000 43299902072089 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240780469/1250000000 : ℝ)^4589 ≤ (12002005661713/100000000000000 : ℝ)^3565 := by
    have hnat : (240780469 : ℕ)^4589*100000000000000^3565 ≤ 12002005661713^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240780469 1250000000 12002005661713 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349636903/10000000000 : ℝ), (5219177403/10000000000 : ℝ), (-240780469/1250000000 : ℝ)] ![(8939618450609/20000000000000 : ℝ), (43299902072089/100000000000000 : ℝ), (12002005661713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349636903/10000000000 : ℝ)|^4589 ≤ (8939618450609/20000000000000 : ℝ)^3565
        have hw : |(5349636903/10000000000 : ℝ)|=(5349636903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219177403/10000000000 : ℝ)|^4589 ≤ (43299902072089/100000000000000 : ℝ)^3565
        have hw : |(5219177403/10000000000 : ℝ)|=(5219177403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240780469/1250000000 : ℝ)|^4589 ≤ (12002005661713/100000000000000 : ℝ)^3565
        have hw : |(-240780469/1250000000 : ℝ)|=(240780469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s6_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531774631/1250000000 : ℝ)*x 0 + (4016523707/10000000000 : ℝ)*x 1 + (4503371123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531774631/1250000000 : ℝ)^4589 ≤ (4160162419619/12500000000000 : ℝ)^3565 := by
    have hnat : (531774631 : ℕ)^4589*12500000000000^3565 ≤ 4160162419619^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531774631 1250000000 4160162419619 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016523707/10000000000 : ℝ)^4589 ≤ (30907329539511/100000000000000 : ℝ)^3565 := by
    have hnat : (4016523707 : ℕ)^4589*100000000000000^3565 ≤ 30907329539511^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016523707 10000000000 30907329539511 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503371123/10000000000 : ℝ)^4589 ≤ (35811371085967/100000000000000 : ℝ)^3565 := by
    have hnat : (4503371123 : ℕ)^4589*100000000000000^3565 ≤ 35811371085967^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503371123 10000000000 35811371085967 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531774631/1250000000 : ℝ), (4016523707/10000000000 : ℝ), (4503371123/10000000000 : ℝ)] ![(4160162419619/12500000000000 : ℝ), (30907329539511/100000000000000 : ℝ), (35811371085967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531774631/1250000000 : ℝ)|^4589 ≤ (4160162419619/12500000000000 : ℝ)^3565
        have hw : |(531774631/1250000000 : ℝ)|=(531774631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016523707/10000000000 : ℝ)|^4589 ≤ (30907329539511/100000000000000 : ℝ)^3565
        have hw : |(4016523707/10000000000 : ℝ)|=(4016523707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503371123/10000000000 : ℝ)|^4589 ≤ (35811371085967/100000000000000 : ℝ)^3565
        have hw : |(4503371123/10000000000 : ℝ)|=(4503371123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s6_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818962151/10000000000 : ℝ)*x 0 + (5220264073/10000000000 : ℝ)*x 1 + (5427748469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818962151/10000000000 : ℝ)^4589 ≤ (2787132532597/25000000000000 : ℝ)^3565 := by
    have hnat : (1818962151 : ℕ)^4589*25000000000000^3565 ≤ 2787132532597^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818962151 10000000000 2787132532597 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220264073/10000000000 : ℝ)^4589 ≤ (5413938413729/12500000000000 : ℝ)^3565 := by
    have hnat : (5220264073 : ℕ)^4589*12500000000000^3565 ≤ 5413938413729^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220264073 10000000000 5413938413729 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427748469/10000000000 : ℝ)^4589 ≤ (22769981272961/50000000000000 : ℝ)^3565 := by
    have hnat : (5427748469 : ℕ)^4589*50000000000000^3565 ≤ 22769981272961^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427748469 10000000000 22769981272961 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818962151/10000000000 : ℝ), (5220264073/10000000000 : ℝ), (5427748469/10000000000 : ℝ)] ![(2787132532597/25000000000000 : ℝ), (5413938413729/12500000000000 : ℝ), (22769981272961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818962151/10000000000 : ℝ)|^4589 ≤ (2787132532597/25000000000000 : ℝ)^3565
        have hw : |(-1818962151/10000000000 : ℝ)|=(1818962151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220264073/10000000000 : ℝ)|^4589 ≤ (5413938413729/12500000000000 : ℝ)^3565
        have hw : |(5220264073/10000000000 : ℝ)|=(5220264073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427748469/10000000000 : ℝ)|^4589 ≤ (22769981272961/50000000000000 : ℝ)^3565
        have hw : |(5427748469/10000000000 : ℝ)|=(5427748469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s6_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254261243/10000000000 : ℝ)*x 0 + (900169603/2000000000 : ℝ)*x 1 + (1004766351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254261243/10000000000 : ℝ)^4589 ≤ (6656389163891/20000000000000 : ℝ)^3565 := by
    have hnat : (4254261243 : ℕ)^4589*20000000000000^3565 ≤ 6656389163891^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254261243 10000000000 6656389163891 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900169603/2000000000 : ℝ)^4589 ≤ (2236596621853/6250000000000 : ℝ)^3565 := by
    have hnat : (900169603 : ℕ)^4589*6250000000000^3565 ≤ 2236596621853^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900169603 2000000000 2236596621853 6250000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004766351/2500000000 : ℝ)^4589 ≤ (30932508216721/100000000000000 : ℝ)^3565 := by
    have hnat : (1004766351 : ℕ)^4589*100000000000000^3565 ≤ 30932508216721^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004766351 2500000000 30932508216721 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254261243/10000000000 : ℝ), (900169603/2000000000 : ℝ), (1004766351/2500000000 : ℝ)] ![(6656389163891/20000000000000 : ℝ), (2236596621853/6250000000000 : ℝ), (30932508216721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254261243/10000000000 : ℝ)|^4589 ≤ (6656389163891/20000000000000 : ℝ)^3565
        have hw : |(4254261243/10000000000 : ℝ)|=(4254261243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900169603/2000000000 : ℝ)|^4589 ≤ (2236596621853/6250000000000 : ℝ)^3565
        have hw : |(900169603/2000000000 : ℝ)|=(900169603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004766351/2500000000 : ℝ)|^4589 ≤ (30932508216721/100000000000000 : ℝ)^3565
        have hw : |(1004766351/2500000000 : ℝ)|=(1004766351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    (11041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (69/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (69/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (69/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (69/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (69/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (69/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (69/625 : ℝ) ^ (4587/1024 : ℝ) ≤ (2582007178777479/50000000000000000000 : ℝ) := by
    have hpowers : (69/625 : ℝ)^4587 ≤ (2582007178777479/50000000000000000000 : ℝ)^1024 := by
      have hnat : (69 : ℕ)^4587*50000000000000000000^1024 ≤ 2582007178777479^1024*625^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69 625 2582007178777479 50000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69/625 : ℝ)) (X := (2582007178777479/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4587/1024 : ℝ) ≤ (11753943451262803/50000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4587 ≤ (11753943451262803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4587*50000000000000000000^1024 ≤ 11753943451262803^1024*20000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 11753943451262803 50000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (11753943451262803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002582007178777479/25000000000000000000 : ℝ) ≤ (10000230553241977/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25002582007178777479/25000000000000000000 : ℝ)^1024 ≤ (10000230553241977/10000000000000000 : ℝ)^4587 := by
      have hnat : (25002582007178777479 : ℕ)^1024*10000000000000000^4587 ≤ 10000230553241977^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002582007178777479 25000000000000000000 10000230553241977 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000230553241977/10000000000000000 : ℝ)) (X := (25002582007178777479/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007167975315020141/25000000000000000000 : ℝ) ≤ (2500159999771259/2500000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25007167975315020141/25000000000000000000 : ℝ)^1024 ≤ (2500159999771259/2500000000000000 : ℝ)^4587 := by
      have hnat : (25007167975315020141 : ℕ)^1024*2500000000000000^4587 ≤ 2500159999771259^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007167975315020141 25000000000000000000 2500159999771259 2500000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500159999771259/2500000000000000 : ℝ)) (X := (25007167975315020141/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011753943451262803/25000000000000000000 : ℝ) ≤ (2000209888985619/2000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25011753943451262803/25000000000000000000 : ℝ)^1024 ≤ (2000209888985619/2000000000000000 : ℝ)^4587 := by
      have hnat : (25011753943451262803 : ℕ)^1024*2000000000000000^4587 ≤ 2000209888985619^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011753943451262803 25000000000000000000 2000209888985619 2000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000209888985619/2000000000000000 : ℝ)) (X := (25011753943451262803/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2582007178777479/50000000000000000000 : ℝ) ≤ ((8888396848989169009/8890000000000000000 : ℝ)+2*(409445843059/444500000000000 : ℝ)*(69/625 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (8888396848989169009/8890000000000000000 : ℝ)+2*(409445843059/444500000000000 : ℝ)*(69/625 : ℝ)=(10000230553241977/10000000000000000 : ℝ) by norm_num, show 1+2*(2582007178777479/50000000000000000000 : ℝ)=(25002582007178777479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11753943451262803/50000000000000000000 : ℝ)+(2582007178777479/50000000000000000000 : ℝ) ≤ ((8888396848989169009/8890000000000000000 : ℝ)+(409445843059/444500000000000 : ℝ)*((3097/20000 : ℝ)+(69/625 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (8888396848989169009/8890000000000000000 : ℝ)+(409445843059/444500000000000 : ℝ)*((3097/20000 : ℝ)+(69/625 : ℝ))=(2500159999771259/2500000000000000 : ℝ) by norm_num, show 1+(11753943451262803/50000000000000000000 : ℝ)+(2582007178777479/50000000000000000000 : ℝ)=(25007167975315020141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11753943451262803/50000000000000000000 : ℝ) ≤ ((8888396848989169009/8890000000000000000 : ℝ)+2*(409445843059/444500000000000 : ℝ)*(3097/20000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (8888396848989169009/8890000000000000000 : ℝ)+2*(409445843059/444500000000000 : ℝ)*(3097/20000 : ℝ)=(2000209888985619/2000000000000000 : ℝ) by norm_num, show 1+2*(11753943451262803/50000000000000000000 : ℝ)=(25011753943451262803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8888396848989169009/8890000000000000000 : ℝ)*(X 1 0+X 2 0)+(409445843059/444500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (69/625 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (8888396848989169009/8890000000000000000 : ℝ)) (alpha := (409445843059/444500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8888396848989169009/8890000000000000000 : ℝ)*(X 0 1+X 2 1)+(409445843059/444500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (69/625 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (8888396848989169009/8890000000000000000 : ℝ)) (alpha := (409445843059/444500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8888396848989169009/8890000000000000000 : ℝ)*(X 0 2+X 1 2)+(409445843059/444500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (69/625 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (8888396848989169009/8890000000000000000 : ℝ)) (alpha := (409445843059/444500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1818934417/10000000000 : ℝ)*X 0 0+(339302703/625000000 : ℝ)*X 0 1+(326198587/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069927381/2000000000 : ℝ)*X 1 0+(-963121863/5000000000 : ℝ)*X 1 1+(260958871/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349636903/10000000000 : ℝ)*X 2 0+(5219177403/10000000000 : ℝ)*X 2 1+(-240780469/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((531774631/1250000000 : ℝ)*X 0 0+(4016523707/10000000000 : ℝ)*X 0 1+(4503371123/10000000000 : ℝ)*X 0 2+(531774631/1250000000 : ℝ)*X 1 0+(4016523707/10000000000 : ℝ)*X 1 1+(4503371123/10000000000 : ℝ)*X 1 2+(531774631/1250000000 : ℝ)*X 2 0+(4016523707/10000000000 : ℝ)*X 2 1+(4503371123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1818962151/10000000000 : ℝ)*X 0 0+(5220264073/10000000000 : ℝ)*X 0 1+(5427748469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4254261243/10000000000 : ℝ)*X 0 0+(900169603/2000000000 : ℝ)*X 0 1+(1004766351/2500000000 : ℝ)*X 0 2+(4254261243/10000000000 : ℝ)*X 1 0+(900169603/2000000000 : ℝ)*X 1 1+(1004766351/2500000000 : ℝ)*X 1 2+(4254261243/10000000000 : ℝ)*X 2 0+(900169603/2000000000 : ℝ)*X 2 1+(1004766351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27067998162968863737665739/5556250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50078071/6250000000000 : ℝ)*(base19) + (753616769/100000000000000 : ℝ)*(base23) + (24527683/100000000000000 : ℝ)*(lower2) + (23718883/20000000000000 : ℝ)*(upper3) + (11946197/20000000000000 : ℝ)*(upper5) + (42647277162657/1250000000000 : ℝ)*(major0) + (42647277162657/1250000000000 : ℝ)*(major1) + (42647277162657/1250000000000 : ℝ)*(major2) + (4769508315116593/100000000000000 : ℝ)*(sp0) + (4769520834182357/100000000000000 : ℝ)*(sp1) + (1192380220453681/25000000000000 : ℝ)*(sp2) + (256754585554539/12500000000000 : ℝ)*(sp3) + (133203149/1000000000000 : ℝ)*(sp4) + (2931884809/50000000000000 : ℝ)*(sp5) + (205404254820593/10000000000000 : ℝ)*(f.failure) + (2384760817715747/50000000000000 : ℝ)*(f.sum) + (13874263807003/4445000000000000000000000000 : ℝ)*base65 + (51420168930768087/11112500000000000000000000000000 : ℝ)*base68 + (70527101287693087/11112500000000000000000000000000 : ℝ)*base70 + (1032189187180587/11112500000000000000000000000000 : ℝ)*base72 + (78058680513/69453125000000000000000000 : ℝ)*base74 + (10436069132606913/11112500000000000000000000000000 : ℝ)*base75 + (36616130853531913/11112500000000000000000000000000 : ℝ)*base77 + (36858019668087/11112500000000000000000000000000 : ℝ)*base80 + (233445999513/277812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1111309/250000000000000000000 : ℝ)*base89 + (1111309/250000000000000000000 : ℝ)*base91 + (1111309/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1546_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1546_box_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-100699457/625000000 : ℝ)*x 0 + (168723969/312500000 : ℝ)*x 1 + (674895971/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100699457/625000000 : ℝ)^4589 ≤ (2384242437321/25000000000000 : ℝ)^3565 := by
    have hnat : (100699457 : ℕ)^4589*25000000000000^3565 ≤ 2384242437321^3565*625000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100699457 625000000 2384242437321 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168723969/312500000 : ℝ)^4589 ≤ (45231511018637/100000000000000 : ℝ)^3565 := by
    have hnat : (168723969 : ℕ)^4589*100000000000000^3565 ≤ 45231511018637^3565*312500000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168723969 312500000 45231511018637 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674895971/1250000000 : ℝ)^4589 ≤ (9046303842869/20000000000000 : ℝ)^3565 := by
    have hnat : (674895971 : ℕ)^4589*20000000000000^3565 ≤ 9046303842869^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674895971 1250000000 9046303842869 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100699457/625000000 : ℝ), (168723969/312500000 : ℝ), (674895971/1250000000 : ℝ)] ![(2384242437321/25000000000000 : ℝ), (45231511018637/100000000000000 : ℝ), (9046303842869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100699457/625000000 : ℝ)|^4589 ≤ (2384242437321/25000000000000 : ℝ)^3565
        have hw : |(-100699457/625000000 : ℝ)|=(100699457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168723969/312500000 : ℝ)|^4589 ≤ (45231511018637/100000000000000 : ℝ)^3565
        have hw : |(168723969/312500000 : ℝ)|=(168723969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674895971/1250000000 : ℝ)|^4589 ≤ (9046303842869/20000000000000 : ℝ)^3565
        have hw : |(674895971/1250000000 : ℝ)|=(674895971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317770307/2500000000 : ℝ)*x 0 + (-223637591/1250000000 : ℝ)*x 1 + (5399167503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317770307/2500000000 : ℝ)^4589 ≤ (43854989164619/100000000000000 : ℝ)^3565 := by
    have hnat : (1317770307 : ℕ)^4589*100000000000000^3565 ≤ 43854989164619^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317770307 2500000000 43854989164619 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223637591/1250000000 : ℝ)^4589 ≤ (2728373615423/25000000000000 : ℝ)^3565 := by
    have hnat : (223637591 : ℕ)^4589*25000000000000^3565 ≤ 2728373615423^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223637591 1250000000 2728373615423 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399167503/10000000000 : ℝ)^4589 ≤ (45231516356631/100000000000000 : ℝ)^3565 := by
    have hnat : (5399167503 : ℕ)^4589*100000000000000^3565 ≤ 45231516356631^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399167503 10000000000 45231516356631 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317770307/2500000000 : ℝ), (-223637591/1250000000 : ℝ), (5399167503/10000000000 : ℝ)] ![(43854989164619/100000000000000 : ℝ), (2728373615423/25000000000000 : ℝ), (45231516356631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317770307/2500000000 : ℝ)|^4589 ≤ (43854989164619/100000000000000 : ℝ)^3565
        have hw : |(1317770307/2500000000 : ℝ)|=(1317770307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223637591/1250000000 : ℝ)|^4589 ≤ (2728373615423/25000000000000 : ℝ)^3565
        have hw : |(-223637591/1250000000 : ℝ)|=(223637591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399167503/10000000000 : ℝ)|^4589 ≤ (45231516356631/100000000000000 : ℝ)^3565
        have hw : |(5399167503/10000000000 : ℝ)|=(5399167503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317770369/2500000000 : ℝ)*x 0 + (107983343/200000000 : ℝ)*x 1 + (-894550437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317770369/2500000000 : ℝ)^4589 ≤ (10963747955157/25000000000000 : ℝ)^3565 := by
    have hnat : (1317770369 : ℕ)^4589*25000000000000^3565 ≤ 10963747955157^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317770369 2500000000 10963747955157 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107983343/200000000 : ℝ)^4589 ≤ (2261575627497/5000000000000 : ℝ)^3565 := by
    have hnat : (107983343 : ℕ)^4589*5000000000000^3565 ≤ 2261575627497^3565*200000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107983343 200000000 2261575627497 5000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894550437/5000000000 : ℝ)^4589 ≤ (1364186951013/12500000000000 : ℝ)^3565 := by
    have hnat : (894550437 : ℕ)^4589*12500000000000^3565 ≤ 1364186951013^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894550437 5000000000 1364186951013 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317770369/2500000000 : ℝ), (107983343/200000000 : ℝ), (-894550437/5000000000 : ℝ)] ![(10963747955157/25000000000000 : ℝ), (2261575627497/5000000000000 : ℝ), (1364186951013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317770369/2500000000 : ℝ)|^4589 ≤ (10963747955157/25000000000000 : ℝ)^3565
        have hw : |(1317770369/2500000000 : ℝ)|=(1317770369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107983343/200000000 : ℝ)|^4589 ≤ (2261575627497/5000000000000 : ℝ)^3565
        have hw : |(107983343/200000000 : ℝ)|=(107983343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-894550437/5000000000 : ℝ)|^4589 ≤ (1364186951013/12500000000000 : ℝ)^3565
        have hw : |(-894550437/5000000000 : ℝ)|=(894550437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (445580901/1000000000 : ℝ)*x 0 + (520020363/1250000000 : ℝ)*x 1 + (4160163221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445580901/1000000000 : ℝ)^4589 ≤ (35325252792353/100000000000000 : ℝ)^3565 := by
    have hnat : (445580901 : ℕ)^4589*100000000000000^3565 ≤ 35325252792353^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445580901 1000000000 35325252792353 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520020363/1250000000 : ℝ)^4589 ≤ (8084343003203/25000000000000 : ℝ)^3565 := by
    have hnat : (520020363 : ℕ)^4589*25000000000000^3565 ≤ 8084343003203^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520020363 1250000000 8084343003203 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160163221/10000000000 : ℝ)^4589 ≤ (16168687592329/50000000000000 : ℝ)^3565 := by
    have hnat : (4160163221 : ℕ)^4589*50000000000000^3565 ≤ 16168687592329^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160163221 10000000000 16168687592329 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445580901/1000000000 : ℝ), (520020363/1250000000 : ℝ), (4160163221/10000000000 : ℝ)] ![(35325252792353/100000000000000 : ℝ), (8084343003203/25000000000000 : ℝ), (16168687592329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445580901/1000000000 : ℝ)|^4589 ≤ (35325252792353/100000000000000 : ℝ)^3565
        have hw : |(445580901/1000000000 : ℝ)|=(445580901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520020363/1250000000 : ℝ)|^4589 ≤ (8084343003203/25000000000000 : ℝ)^3565
        have hw : |(520020363/1250000000 : ℝ)|=(520020363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4160163221/10000000000 : ℝ)|^4589 ≤ (16168687592329/50000000000000 : ℝ)^3565
        have hw : |(4160163221/10000000000 : ℝ)|=(4160163221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-203208577/1000000000 : ℝ)*x 0 + (5244566579/10000000000 : ℝ)*x 1 + (5244567969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203208577/1000000000 : ℝ)^4589 ≤ (12857524555123/100000000000000 : ℝ)^3565 := by
    have hnat : (203208577 : ℕ)^4589*100000000000000^3565 ≤ 12857524555123^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203208577 1000000000 12857524555123 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244566579/10000000000 : ℝ)^4589 ≤ (21785615140227/50000000000000 : ℝ)^3565 := by
    have hnat : (5244566579 : ℕ)^4589*50000000000000^3565 ≤ 21785615140227^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244566579 10000000000 21785615140227 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244567969/10000000000 : ℝ)^4589 ≤ (43571245145407/100000000000000 : ℝ)^3565 := by
    have hnat : (5244567969 : ℕ)^4589*100000000000000^3565 ≤ 43571245145407^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244567969 10000000000 43571245145407 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203208577/1000000000 : ℝ), (5244566579/10000000000 : ℝ), (5244567969/10000000000 : ℝ)] ![(12857524555123/100000000000000 : ℝ), (21785615140227/50000000000000 : ℝ), (43571245145407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203208577/1000000000 : ℝ)|^4589 ≤ (12857524555123/100000000000000 : ℝ)^3565
        have hw : |(-203208577/1000000000 : ℝ)|=(203208577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244566579/10000000000 : ℝ)|^4589 ≤ (21785615140227/50000000000000 : ℝ)^3565
        have hw : |(5244566579/10000000000 : ℝ)|=(5244566579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244567969/10000000000 : ℝ)|^4589 ≤ (43571245145407/100000000000000 : ℝ)^3565
        have hw : |(5244567969/10000000000 : ℝ)|=(5244567969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075687763/2000000000 : ℝ)*x 0 + (-1853361259/10000000000 : ℝ)*x 1 + (524456723/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075687763/2000000000 : ℝ)^4589 ≤ (4500810515943/10000000000000 : ℝ)^3565 := by
    have hnat : (1075687763 : ℕ)^4589*10000000000000^3565 ≤ 4500810515943^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075687763 2000000000 4500810515943 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853361259/10000000000 : ℝ)^4589 ≤ (1427582198731/12500000000000 : ℝ)^3565 := by
    have hnat : (1853361259 : ℕ)^4589*12500000000000^3565 ≤ 1427582198731^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853361259 10000000000 1427582198731 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524456723/1000000000 : ℝ)^4589 ≤ (8714247448477/20000000000000 : ℝ)^3565 := by
    have hnat : (524456723 : ℕ)^4589*20000000000000^3565 ≤ 8714247448477^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524456723 1000000000 8714247448477 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075687763/2000000000 : ℝ), (-1853361259/10000000000 : ℝ), (524456723/1000000000 : ℝ)] ![(4500810515943/10000000000000 : ℝ), (1427582198731/12500000000000 : ℝ), (8714247448477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075687763/2000000000 : ℝ)|^4589 ≤ (4500810515943/10000000000000 : ℝ)^3565
        have hw : |(1075687763/2000000000 : ℝ)|=(1075687763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853361259/10000000000 : ℝ)|^4589 ≤ (1427582198731/12500000000000 : ℝ)^3565
        have hw : |(-1853361259/10000000000 : ℝ)|=(1853361259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524456723/1000000000 : ℝ)|^4589 ≤ (8714247448477/20000000000000 : ℝ)^3565
        have hw : |(524456723/1000000000 : ℝ)|=(524456723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672304723/1250000000 : ℝ)*x 0 + (40973187/78125000 : ℝ)*x 1 + (-1853361707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672304723/1250000000 : ℝ)^4589 ≤ (45008094053583/100000000000000 : ℝ)^3565 := by
    have hnat : (672304723 : ℕ)^4589*100000000000000^3565 ≤ 45008094053583^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672304723 1250000000 45008094053583 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40973187/78125000 : ℝ)^4589 ≤ (21785622396249/50000000000000 : ℝ)^3565 := by
    have hnat : (40973187 : ℕ)^4589*50000000000000^3565 ≤ 21785622396249^3565*78125000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40973187 78125000 21785622396249 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853361707/10000000000 : ℝ)^4589 ≤ (11420661143441/100000000000000 : ℝ)^3565 := by
    have hnat : (1853361707 : ℕ)^4589*100000000000000^3565 ≤ 11420661143441^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853361707 10000000000 11420661143441 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672304723/1250000000 : ℝ), (40973187/78125000 : ℝ), (-1853361707/10000000000 : ℝ)] ![(45008094053583/100000000000000 : ℝ), (21785622396249/50000000000000 : ℝ), (11420661143441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672304723/1250000000 : ℝ)|^4589 ≤ (45008094053583/100000000000000 : ℝ)^3565
        have hw : |(672304723/1250000000 : ℝ)|=(672304723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40973187/78125000 : ℝ)|^4589 ≤ (21785622396249/50000000000000 : ℝ)^3565
        have hw : |(40973187/78125000 : ℝ)|=(40973187/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1853361707/10000000000 : ℝ)|^4589 ≤ (11420661143441/100000000000000 : ℝ)^3565
        have hw : |(-1853361707/10000000000 : ℝ)|=(1853361707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (7910167/19531250 : ℝ)*x 0 + (872587031/2000000000 : ℝ)*x 1 + (272683391/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7910167/19531250 : ℝ)^4589 ≤ (31239374608017/100000000000000 : ℝ)^3565 := by
    have hnat : (7910167 : ℕ)^4589*100000000000000^3565 ≤ 31239374608017^3565*19531250^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7910167 19531250 31239374608017 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872587031/2000000000 : ℝ)^4589 ≤ (34380317244937/100000000000000 : ℝ)^3565 := by
    have hnat : (872587031 : ℕ)^4589*100000000000000^3565 ≤ 34380317244937^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872587031 2000000000 34380317244937 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272683391/625000000 : ℝ)^4589 ≤ (34380308125893/100000000000000 : ℝ)^3565 := by
    have hnat : (272683391 : ℕ)^4589*100000000000000^3565 ≤ 34380308125893^3565*625000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272683391 625000000 34380308125893 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7910167/19531250 : ℝ), (872587031/2000000000 : ℝ), (272683391/625000000 : ℝ)] ![(31239374608017/100000000000000 : ℝ), (34380317244937/100000000000000 : ℝ), (34380308125893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7910167/19531250 : ℝ)|^4589 ≤ (31239374608017/100000000000000 : ℝ)^3565
        have hw : |(7910167/19531250 : ℝ)|=(7910167/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872587031/2000000000 : ℝ)|^4589 ≤ (34380317244937/100000000000000 : ℝ)^3565
        have hw : |(872587031/2000000000 : ℝ)|=(872587031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272683391/625000000 : ℝ)|^4589 ≤ (34380308125893/100000000000000 : ℝ)^3565
        have hw : |(272683391/625000000 : ℝ)|=(272683391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_8 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388594909/2000000000 : ℝ)*x 0 + (5135896781/10000000000 : ℝ)*x 1 + (541951603/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388594909/2000000000 : ℝ)^4589 ≤ (1517045241333/12500000000000 : ℝ)^3565 := by
    have hnat : (388594909 : ℕ)^4589*12500000000000^3565 ≤ 1517045241333^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388594909 2000000000 1517045241333 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135896781/10000000000 : ℝ)^4589 ≤ (4241256806023/10000000000000 : ℝ)^3565 := by
    have hnat : (5135896781 : ℕ)^4589*10000000000000^3565 ≤ 4241256806023^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135896781 10000000000 4241256806023 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541951603/1000000000 : ℝ)^4589 ≤ (45451069998241/100000000000000 : ℝ)^3565 := by
    have hnat : (541951603 : ℕ)^4589*100000000000000^3565 ≤ 45451069998241^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541951603 1000000000 45451069998241 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388594909/2000000000 : ℝ), (5135896781/10000000000 : ℝ), (541951603/1000000000 : ℝ)] ![(1517045241333/12500000000000 : ℝ), (4241256806023/10000000000000 : ℝ), (45451069998241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388594909/2000000000 : ℝ)|^4589 ≤ (1517045241333/12500000000000 : ℝ)^3565
        have hw : |(-388594909/2000000000 : ℝ)|=(388594909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135896781/10000000000 : ℝ)|^4589 ≤ (4241256806023/10000000000000 : ℝ)^3565
        have hw : |(5135896781/10000000000 : ℝ)|=(5135896781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541951603/1000000000 : ℝ)|^4589 ≤ (45451069998241/100000000000000 : ℝ)^3565
        have hw : |(541951603/1000000000 : ℝ)|=(541951603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_9 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210277851/400000000 : ℝ)*x 0 + (-1780405197/10000000000 : ℝ)*x 1 + (2709758017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210277851/400000000 : ℝ)^4589 ≤ (43703666216553/100000000000000 : ℝ)^3565 := by
    have hnat : (210277851 : ℕ)^4589*100000000000000^3565 ≤ 43703666216553^3565*400000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210277851 400000000 43703666216553 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780405197/10000000000 : ℝ)^4589 ≤ (433810548969/4000000000000 : ℝ)^3565 := by
    have hnat : (1780405197 : ℕ)^4589*4000000000000^3565 ≤ 433810548969^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780405197 10000000000 433810548969 4000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709758017/5000000000 : ℝ)^4589 ≤ (45451070041423/100000000000000 : ℝ)^3565 := by
    have hnat : (2709758017 : ℕ)^4589*100000000000000^3565 ≤ 45451070041423^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709758017 5000000000 45451070041423 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210277851/400000000 : ℝ), (-1780405197/10000000000 : ℝ), (2709758017/5000000000 : ℝ)] ![(43703666216553/100000000000000 : ℝ), (433810548969/4000000000000 : ℝ), (45451070041423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210277851/400000000 : ℝ)|^4589 ≤ (43703666216553/100000000000000 : ℝ)^3565
        have hw : |(210277851/400000000 : ℝ)|=(210277851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780405197/10000000000 : ℝ)|^4589 ≤ (433810548969/4000000000000 : ℝ)^3565
        have hw : |(-1780405197/10000000000 : ℝ)|=(1780405197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709758017/5000000000 : ℝ)|^4589 ≤ (45451070041423/100000000000000 : ℝ)^3565
        have hw : |(2709758017/5000000000 : ℝ)|=(2709758017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_10 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256946367/10000000000 : ℝ)*x 0 + (5419515989/10000000000 : ℝ)*x 1 + (-356081027/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256946367/10000000000 : ℝ)^4589 ≤ (43703667201087/100000000000000 : ℝ)^3565 := by
    have hnat : (5256946367 : ℕ)^4589*100000000000000^3565 ≤ 43703667201087^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256946367 10000000000 43703667201087 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419515989/10000000000 : ℝ)^4589 ≤ (22725534777813/50000000000000 : ℝ)^3565 := by
    have hnat : (5419515989 : ℕ)^4589*50000000000000^3565 ≤ 22725534777813^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419515989 10000000000 22725534777813 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356081027/2000000000 : ℝ)^4589 ≤ (5422631619037/50000000000000 : ℝ)^3565 := by
    have hnat : (356081027 : ℕ)^4589*50000000000000^3565 ≤ 5422631619037^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356081027 2000000000 5422631619037 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256946367/10000000000 : ℝ), (5419515989/10000000000 : ℝ), (-356081027/2000000000 : ℝ)] ![(43703667201087/100000000000000 : ℝ), (22725534777813/50000000000000 : ℝ), (5422631619037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256946367/10000000000 : ℝ)|^4589 ≤ (43703667201087/100000000000000 : ℝ)^3565
        have hw : |(5256946367/10000000000 : ℝ)|=(5256946367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419515989/10000000000 : ℝ)|^4589 ≤ (22725534777813/50000000000000 : ℝ)^3565
        have hw : |(5419515989/10000000000 : ℝ)|=(5419515989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356081027/2000000000 : ℝ)|^4589 ≤ (5422631619037/50000000000000 : ℝ)^3565
        have hw : |(-356081027/2000000000 : ℝ)|=(356081027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_11 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4508072537/10000000000 : ℝ)*x 0 + (2066720699/5000000000 : ℝ)*x 1 + (4133441409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4508072537/10000000000 : ℝ)^4589 ≤ (35859503242963/100000000000000 : ℝ)^3565 := by
    have hnat : (4508072537 : ℕ)^4589*100000000000000^3565 ≤ 35859503242963^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508072537 10000000000 35859503242963 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066720699/5000000000 : ℝ)^4589 ≤ (16035124160001/50000000000000 : ℝ)^3565 := by
    have hnat : (2066720699 : ℕ)^4589*50000000000000^3565 ≤ 16035124160001^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066720699 5000000000 16035124160001 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133441409/10000000000 : ℝ)^4589 ≤ (32070248429863/100000000000000 : ℝ)^3565 := by
    have hnat : (4133441409 : ℕ)^4589*100000000000000^3565 ≤ 32070248429863^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133441409 10000000000 32070248429863 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4508072537/10000000000 : ℝ), (2066720699/5000000000 : ℝ), (4133441409/10000000000 : ℝ)] ![(35859503242963/100000000000000 : ℝ), (16035124160001/50000000000000 : ℝ), (32070248429863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4508072537/10000000000 : ℝ)|^4589 ≤ (35859503242963/100000000000000 : ℝ)^3565
        have hw : |(4508072537/10000000000 : ℝ)|=(4508072537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2066720699/5000000000 : ℝ)|^4589 ≤ (16035124160001/50000000000000 : ℝ)^3565
        have hw : |(2066720699/5000000000 : ℝ)|=(2066720699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133441409/10000000000 : ℝ)|^4589 ≤ (32070248429863/100000000000000 : ℝ)^3565
        have hw : |(4133441409/10000000000 : ℝ)|=(4133441409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_12 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1700076621/10000000000 : ℝ)*x 0 + (1376113483/2500000000 : ℝ)*x 1 + (1307380497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1700076621/10000000000 : ℝ)^4589 ≤ (2043904262581/20000000000000 : ℝ)^3565 := by
    have hnat : (1700076621 : ℕ)^4589*20000000000000^3565 ≤ 2043904262581^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700076621 10000000000 2043904262581 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376113483/2500000000 : ℝ)^4589 ≤ (46370072082107/100000000000000 : ℝ)^3565 := by
    have hnat : (1376113483 : ℕ)^4589*100000000000000^3565 ≤ 46370072082107^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376113483 2500000000 46370072082107 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307380497/2500000000 : ℝ)^4589 ≤ (21705203290669/50000000000000 : ℝ)^3565 := by
    have hnat : (1307380497 : ℕ)^4589*50000000000000^3565 ≤ 21705203290669^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307380497 2500000000 21705203290669 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1700076621/10000000000 : ℝ), (1376113483/2500000000 : ℝ), (1307380497/2500000000 : ℝ)] ![(2043904262581/20000000000000 : ℝ), (46370072082107/100000000000000 : ℝ), (21705203290669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1700076621/10000000000 : ℝ)|^4589 ≤ (2043904262581/20000000000000 : ℝ)^3565
        have hw : |(-1700076621/10000000000 : ℝ)|=(1700076621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376113483/2500000000 : ℝ)|^4589 ≤ (46370072082107/100000000000000 : ℝ)^3565
        have hw : |(1376113483/2500000000 : ℝ)|=(1376113483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307380497/2500000000 : ℝ)|^4589 ≤ (21705203290669/50000000000000 : ℝ)^3565
        have hw : |(1307380497/2500000000 : ℝ)|=(1307380497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_13 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347221733/2500000000 : ℝ)*x 0 + (-371888369/2000000000 : ℝ)*x 1 + (653690229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347221733/2500000000 : ℝ)^4589 ≤ (45120682799361/100000000000000 : ℝ)^3565 := by
    have hnat : (1347221733 : ℕ)^4589*100000000000000^3565 ≤ 45120682799361^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347221733 2500000000 45120682799361 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371888369/2000000000 : ℝ)^4589 ≤ (2293782453451/20000000000000 : ℝ)^3565 := by
    have hnat : (371888369 : ℕ)^4589*20000000000000^3565 ≤ 2293782453451^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371888369 2000000000 2293782453451 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653690229/1250000000 : ℝ)^4589 ≤ (43410404914417/100000000000000 : ℝ)^3565 := by
    have hnat : (653690229 : ℕ)^4589*100000000000000^3565 ≤ 43410404914417^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653690229 1250000000 43410404914417 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347221733/2500000000 : ℝ), (-371888369/2000000000 : ℝ), (653690229/1250000000 : ℝ)] ![(45120682799361/100000000000000 : ℝ), (2293782453451/20000000000000 : ℝ), (43410404914417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347221733/2500000000 : ℝ)|^4589 ≤ (45120682799361/100000000000000 : ℝ)^3565
        have hw : |(1347221733/2500000000 : ℝ)|=(1347221733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-371888369/2000000000 : ℝ)|^4589 ≤ (2293782453451/20000000000000 : ℝ)^3565
        have hw : |(-371888369/2000000000 : ℝ)|=(371888369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653690229/1250000000 : ℝ)|^4589 ≤ (43410404914417/100000000000000 : ℝ)^3565
        have hw : |(653690229/1250000000 : ℝ)|=(653690229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_14 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388887077/10000000000 : ℝ)*x 0 + (261476087/500000000 : ℝ)*x 1 + (-464860443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388887077/10000000000 : ℝ)^4589 ≤ (564008554527/1250000000000 : ℝ)^3565 := by
    have hnat : (5388887077 : ℕ)^4589*1250000000000^3565 ≤ 564008554527^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388887077 10000000000 564008554527 1250000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261476087/500000000 : ℝ)^4589 ≤ (43410403931361/100000000000000 : ℝ)^3565 := by
    have hnat : (261476087 : ℕ)^4589*100000000000000^3565 ≤ 43410403931361^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261476087 500000000 43410403931361 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464860443/2500000000 : ℝ)^4589 ≤ (2293782337533/20000000000000 : ℝ)^3565 := by
    have hnat : (464860443 : ℕ)^4589*20000000000000^3565 ≤ 2293782337533^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464860443 2500000000 2293782337533 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388887077/10000000000 : ℝ), (261476087/500000000 : ℝ), (-464860443/2500000000 : ℝ)] ![(564008554527/1250000000000 : ℝ), (43410403931361/100000000000000 : ℝ), (2293782337533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388887077/10000000000 : ℝ)|^4589 ≤ (564008554527/1250000000000 : ℝ)^3565
        have hw : |(5388887077/10000000000 : ℝ)|=(5388887077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261476087/500000000 : ℝ)|^4589 ≤ (43410403931361/100000000000000 : ℝ)^3565
        have hw : |(261476087/500000000 : ℝ)|=(261476087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464860443/2500000000 : ℝ)|^4589 ≤ (2293782337533/20000000000000 : ℝ)^3565
        have hw : |(-464860443/2500000000 : ℝ)|=(464860443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_box_15 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2004824761/5000000000 : ℝ)*x 0 + (4382644911/10000000000 : ℝ)*x 1 + (4382644691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004824761/5000000000 : ℝ)^4589 ≤ (15419627549447/50000000000000 : ℝ)^3565 := by
    have hnat : (2004824761 : ℕ)^4589*50000000000000^3565 ≤ 15419627549447^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004824761 5000000000 15419627549447 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4382644911/10000000000 : ℝ)^4589 ≤ (34580373563003/100000000000000 : ℝ)^3565 := by
    have hnat : (4382644911 : ℕ)^4589*100000000000000^3565 ≤ 34580373563003^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382644911 10000000000 34580373563003 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382644691/10000000000 : ℝ)^4589 ≤ (34580371328533/100000000000000 : ℝ)^3565 := by
    have hnat : (4382644691 : ℕ)^4589*100000000000000^3565 ≤ 34580371328533^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382644691 10000000000 34580371328533 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2004824761/5000000000 : ℝ), (4382644911/10000000000 : ℝ), (4382644691/10000000000 : ℝ)] ![(15419627549447/50000000000000 : ℝ), (34580373563003/100000000000000 : ℝ), (34580371328533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2004824761/5000000000 : ℝ)|^4589 ≤ (15419627549447/50000000000000 : ℝ)^3565
        have hw : |(2004824761/5000000000 : ℝ)|=(2004824761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4382644911/10000000000 : ℝ)|^4589 ≤ (34580373563003/100000000000000 : ℝ)^3565
        have hw : |(4382644911/10000000000 : ℝ)|=(4382644911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382644691/10000000000 : ℝ)|^4589 ≤ (34580371328533/100000000000000 : ℝ)^3565
        have hw : |(4382644691/10000000000 : ℝ)|=(4382644691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15947/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14697/25000 : ℝ) ∧ (80677/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43109/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11041/100000 : ℝ) ^ (4587/1024 : ℝ) ≤ (5166109992296043/100000000000000000000 : ℝ) := by
    have hpowers : (11041/100000 : ℝ)^4587 ≤ (5166109992296043/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11041 : ℕ)^4587*100000000000000000000^1024 ≤ 5166109992296043^1024*100000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11041 100000 5166109992296043 100000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11041/100000 : ℝ)) (X := (5166109992296043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4587/1024 : ℝ) ≤ (11753943451262803/50000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4587 ≤ (11753943451262803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4587*50000000000000000000^1024 ≤ 11753943451262803^1024*20000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 11753943451262803 50000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (11753943451262803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005166109992296043/50000000000000000000 : ℝ) ≤ (5000115323400099/5000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (50005166109992296043/50000000000000000000 : ℝ)^1024 ≤ (5000115323400099/5000000000000000 : ℝ)^4587 := by
      have hnat : (50005166109992296043 : ℕ)^1024*5000000000000000^4587 ≤ 5000115323400099^4587*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005166109992296043 50000000000000000000 5000115323400099 5000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000115323400099/5000000000000000 : ℝ)) (X := (50005166109992296043/50000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028673996894821649/100000000000000000000 : ℝ) ≤ (10000640045857483/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (100028673996894821649/100000000000000000000 : ℝ)^1024 ≤ (10000640045857483/10000000000000000 : ℝ)^4587 := by
      have hnat : (100028673996894821649 : ℕ)^1024*10000000000000000^4587 ≤ 10000640045857483^4587*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028673996894821649 100000000000000000000 10000640045857483 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000640045857483/10000000000000000 : ℝ)) (X := (100028673996894821649/100000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011753943451262803/25000000000000000000 : ℝ) ≤ (625065590307173/625000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25011753943451262803/25000000000000000000 : ℝ)^1024 ≤ (625065590307173/625000000000000 : ℝ)^4587 := by
      have hnat : (25011753943451262803 : ℕ)^1024*625000000000000^4587 ≤ 625065590307173^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011753943451262803 25000000000000000000 625065590307173 625000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625065590307173/625000000000000 : ℝ)) (X := (25011753943451262803/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5166109992296043/100000000000000000000 : ℝ) ≤ ((22215992322198556271/22220000000000000000 : ℝ)+2*(81879811457/88880000000000 : ℝ)*(11041/100000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (22215992322198556271/22220000000000000000 : ℝ)+2*(81879811457/88880000000000 : ℝ)*(11041/100000 : ℝ)=(5000115323400099/5000000000000000 : ℝ) by norm_num, show 1+2*(5166109992296043/100000000000000000000 : ℝ)=(50005166109992296043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11753943451262803/50000000000000000000 : ℝ)+(5166109992296043/100000000000000000000 : ℝ) ≤ ((22215992322198556271/22220000000000000000 : ℝ)+(81879811457/88880000000000 : ℝ)*((3097/20000 : ℝ)+(11041/100000 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (22215992322198556271/22220000000000000000 : ℝ)+(81879811457/88880000000000 : ℝ)*((3097/20000 : ℝ)+(11041/100000 : ℝ))=(10000640045857483/10000000000000000 : ℝ) by norm_num, show 1+(11753943451262803/50000000000000000000 : ℝ)+(5166109992296043/100000000000000000000 : ℝ)=(100028673996894821649/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11753943451262803/50000000000000000000 : ℝ) ≤ ((22215992322198556271/22220000000000000000 : ℝ)+2*(81879811457/88880000000000 : ℝ)*(3097/20000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (22215992322198556271/22220000000000000000 : ℝ)+2*(81879811457/88880000000000 : ℝ)*(3097/20000 : ℝ)=(625065590307173/625000000000000 : ℝ) by norm_num, show 1+2*(11753943451262803/50000000000000000000 : ℝ)=(25011753943451262803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22215992322198556271/22220000000000000000 : ℝ)*(X 1 0+X 2 0)+(81879811457/88880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22215992322198556271/22220000000000000000 : ℝ)) (alpha := (81879811457/88880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22215992322198556271/22220000000000000000 : ℝ)*(X 0 1+X 2 1)+(81879811457/88880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22215992322198556271/22220000000000000000 : ℝ)) (alpha := (81879811457/88880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22215992322198556271/22220000000000000000 : ℝ)*(X 0 2+X 1 2)+(81879811457/88880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22215992322198556271/22220000000000000000 : ℝ)) (alpha := (81879811457/88880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-100699457/625000000 : ℝ)*X 0 0+(168723969/312500000 : ℝ)*X 0 1+(674895971/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317770307/2500000000 : ℝ)*X 1 0+(-223637591/1250000000 : ℝ)*X 1 1+(5399167503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317770369/2500000000 : ℝ)*X 2 0+(107983343/200000000 : ℝ)*X 2 1+(-894550437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((445580901/1000000000 : ℝ)*X 0 0+(520020363/1250000000 : ℝ)*X 0 1+(4160163221/10000000000 : ℝ)*X 0 2+(445580901/1000000000 : ℝ)*X 1 0+(520020363/1250000000 : ℝ)*X 1 1+(4160163221/10000000000 : ℝ)*X 1 2+(445580901/1000000000 : ℝ)*X 2 0+(520020363/1250000000 : ℝ)*X 2 1+(4160163221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-203208577/1000000000 : ℝ)*X 0 0+(5244566579/10000000000 : ℝ)*X 0 1+(5244567969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1075687763/2000000000 : ℝ)*X 1 0+(-1853361259/10000000000 : ℝ)*X 1 1+(524456723/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672304723/1250000000 : ℝ)*X 2 0+(40973187/78125000 : ℝ)*X 2 1+(-1853361707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((7910167/19531250 : ℝ)*X 0 0+(872587031/2000000000 : ℝ)*X 0 1+(272683391/625000000 : ℝ)*X 0 2+(7910167/19531250 : ℝ)*X 1 0+(872587031/2000000000 : ℝ)*X 1 1+(272683391/625000000 : ℝ)*X 1 2+(7910167/19531250 : ℝ)*X 2 0+(872587031/2000000000 : ℝ)*X 2 1+(272683391/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-388594909/2000000000 : ℝ)*X 0 0+(5135896781/10000000000 : ℝ)*X 0 1+(541951603/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((210277851/400000000 : ℝ)*X 1 0+(-1780405197/10000000000 : ℝ)*X 1 1+(2709758017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256946367/10000000000 : ℝ)*X 2 0+(5419515989/10000000000 : ℝ)*X 2 1+(-356081027/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4508072537/10000000000 : ℝ)*X 0 0+(2066720699/5000000000 : ℝ)*X 0 1+(4133441409/10000000000 : ℝ)*X 0 2+(4508072537/10000000000 : ℝ)*X 1 0+(2066720699/5000000000 : ℝ)*X 1 1+(4133441409/10000000000 : ℝ)*X 1 2+(4508072537/10000000000 : ℝ)*X 2 0+(2066720699/5000000000 : ℝ)*X 2 1+(4133441409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1700076621/10000000000 : ℝ)*X 0 0+(1376113483/2500000000 : ℝ)*X 0 1+(1307380497/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1347221733/2500000000 : ℝ)*X 1 0+(-371888369/2000000000 : ℝ)*X 1 1+(653690229/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5388887077/10000000000 : ℝ)*X 2 0+(261476087/500000000 : ℝ)*X 2 1+(-464860443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2004824761/5000000000 : ℝ)*X 0 0+(4382644911/10000000000 : ℝ)*X 0 1+(4382644691/10000000000 : ℝ)*X 0 2+(2004824761/5000000000 : ℝ)*X 1 0+(4382644911/10000000000 : ℝ)*X 1 1+(4382644691/10000000000 : ℝ)*X 1 2+(2004824761/5000000000 : ℝ)*X 2 0+(4382644911/10000000000 : ℝ)*X 2 1+(4382644691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15947/25000 : ℝ) ≤ (-8858282559362360858906471561679/13887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18681071/50000000000000 : ℝ)*(lower0) + (243024999/100000000000000 : ℝ)*(upper1) + (305689729/100000000000000 : ℝ)*(lower4) + (28414465670071/1250000000000 : ℝ)*(major0) + (28414465670071/1250000000000 : ℝ)*(major1) + (2273157253605681/100000000000000 : ℝ)*(major2) + (542205253/25000000000000 : ℝ)*(sp3) + (799755797945293/25000000000000 : ℝ)*(sp4) + (3199018793769721/100000000000000 : ℝ)*(sp5) + (49984307849859/1562500000000 : ℝ)*(sp6) + (684269112350941/50000000000000 : ℝ)*(sp7) + (3231562547/25000000000000 : ℝ)*(sp12) + (17324261639/100000000000000 : ℝ)*(sp13) + (631494381/1562500000000 : ℝ)*(sp14) + (684270196761447/50000000000000 : ℝ)*(f.failure) + (3199036118031359/100000000000000 : ℝ)*(f.sum) + (67467146762497/8888000000000000000000000000 : ℝ)*base65 + (172229714108965817/13887500000000000000000000000000 : ℝ)*base68 + (1178575190231775551/2222000000000000000000000000000000 : ℝ)*base69 + (66341810194453317/13887500000000000000000000000000 : ℝ)*base72 + (1334915938451/1777600000000000000000000000 : ℝ)*base74 + (3465031660420224449/2222000000000000000000000000000000 : ℝ)*base76 + (352968394959184759/27775000000000000000000000000000 : ℝ)*base78 + (342223993229034759/27775000000000000000000000000000 : ℝ)*base80 + (303963155371/69437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3136789/1250000000000000000000 : ℝ)*base90 + (3136789/1250000000000000000000 : ℝ)*base92 + (15636789/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14697/25000 : ℝ) ≤ (29689346537569922626112472146613/50500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6582863/20000000000000 : ℝ)*(lower0) + (76074301/100000000000000 : ℝ)*(lower1) + (3643859/100000000000000 : ℝ)*(lower3) + (2351734035873223/100000000000000 : ℝ)*(major0) + (2351734035873223/100000000000000 : ℝ)*(major1) + (293966754484153/12500000000000 : ℝ)*(major2) + (408501695057801/12500000000000 : ℝ)*(sp0) + (3268022823479137/100000000000000 : ℝ)*(sp1) + (81699407066687/2500000000000 : ℝ)*(sp2) + (1415844760934721/100000000000000 : ℝ)*(sp3) + (1256129239/100000000000000 : ℝ)*(sp5) + (1151397853/50000000000000 : ℝ)*(sp7) + (1493654403/3125000000000 : ℝ)*(sp10) + (657446623/6250000000000 : ℝ)*(sp12) + (353961765932607/25000000000000 : ℝ)*(f.failure) + (408503009951047/12500000000000 : ℝ)*(f.sum) + (12473780477599/8888000000000000000000000000 : ℝ)*base65 + (4781954527958368567/2222000000000000000000000000000000 : ℝ)*base68 + (197111450180158383/25250000000000000000000000000000 : ℝ)*base69 + (8851855054980368567/2222000000000000000000000000000000 : ℝ)*base72 + (15894043154903/8888000000000000000000000000 : ℝ)*base73 + (239877043066908383/25250000000000000000000000000000 : ℝ)*base75 + (4988654060446618567/2222000000000000000000000000000000 : ℝ)*base78 + (9717236737110618567/2222000000000000000000000000000000 : ℝ)*base80 + (29036677105157/4444000000000000000000000000 : ℝ)*base82 + (5570291/625000000000000000000 : ℝ)*base89 + (5570291/625000000000000000000 : ℝ)*base91 + (679709/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80677/100000 : ℝ) ≤ (448173535452083607174412379975709/555500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1434793/10000000000000 : ℝ)*(lower2) + (23161577/50000000000000 : ℝ)*(lower3) + (128493/1250000000000 : ℝ)*(upper4) + (4493853/25000000000000 : ℝ)*(lower5) + (1270694718839793/50000000000000 : ℝ)*(major0) + (1270694718839793/50000000000000 : ℝ)*(major1) + (1270694718839793/50000000000000 : ℝ)*(major2) + (12096599013/25000000000000 : ℝ)*(sp1) + (21430121157/50000000000000 : ℝ)*(sp2) + (2899472567/100000000000000 : ℝ)*(sp4) + (440731867295211/12500000000000 : ℝ)*(sp8) + (881452362859551/25000000000000 : ℝ)*(sp9) + (1762907488795971/50000000000000 : ℝ)*(sp10) + (38250698402191/2500000000000 : ℝ)*(sp11) + (38250698402191/2500000000000 : ℝ)*(f.failure) + (220366114864641/6250000000000 : ℝ)*(f.sum) + (8973365638459/2222000000000000000000000000 : ℝ)*base66 + (1412959918006258097/1111000000000000000000000000000000 : ℝ)*base68 + (2464913942491741903/1111000000000000000000000000000000 : ℝ)*base69 + (23283171894751258097/1111000000000000000000000000000000 : ℝ)*base72 + (1109284449671/2222000000000000000000000000 : ℝ)*base74 + (2189612554272741903/1111000000000000000000000000000000 : ℝ)*base75 + (5419567569393258097/1111000000000000000000000000000000 : ℝ)*base78 + (2242744838993258097/1111000000000000000000000000000000 : ℝ)*base80 + (108746006213/2222000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (308317/62500000000000000000 : ℝ)*base90 + (308317/62500000000000000000 : ℝ)*base92 + (308317/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-43109/50000 : ℝ) ≤ (-957848860737243481800897173771703/1111000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9370869/25000000000000 : ℝ)*(upper1) + (17101919/50000000000000 : ℝ)*(lower2) + (766267/5000000000000 : ℝ)*(upper3) + (55954327/100000000000000 : ℝ)*(upper5) + (1290642199871367/50000000000000 : ℝ)*(major0) + (1290642199871367/50000000000000 : ℝ)*(major1) + (516256879948547/20000000000000 : ℝ)*(major2) + (2873231643/12500000000000 : ℝ)*(sp5) + (2545168053/6250000000000 : ℝ)*(sp6) + (2820941441/50000000000000 : ℝ)*(sp7) + (3637260685639467/100000000000000 : ℝ)*(sp12) + (3637237699786323/100000000000000 : ℝ)*(sp13) + (1818609981475309/50000000000000 : ℝ)*(sp14) + (388510202904799/25000000000000 : ℝ)*(sp15) + (777023226751039/50000000000000 : ℝ)*(f.failure) + (3637260685639467/100000000000000 : ℝ)*(f.sum) + (3523250225371/8888000000000000000000000000 : ℝ)*base66 + (9308674489936932543/1111000000000000000000000000000000 : ℝ)*base68 + (1035448913569511763/444400000000000000000000000000000 : ℝ)*base70 + (9989783845522932543/1111000000000000000000000000000000 : ℝ)*base72 + (9250688235253/8888000000000000000000000000 : ℝ)*base73 + (1907039283593511763/444400000000000000000000000000000 : ℝ)*base76 + (1663724662602942457/1111000000000000000000000000000000 : ℝ)*base77 + (10697081417613057543/1111000000000000000000000000000000 : ℝ)*base80 + (19144190842593/2222000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17446307/1250000000000000000000 : ℝ)*base89 + (17446307/1250000000000000000000 : ℝ)*base91 + (4946307/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1546_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15947/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14697/25000 : ℝ) else (80677/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43109/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1546_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1546_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15947/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14697/25000 : ℝ) else (80677/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43109/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1546_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1546_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15947/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(14697/25000 : ℝ) else (80677/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43109/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1546_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
