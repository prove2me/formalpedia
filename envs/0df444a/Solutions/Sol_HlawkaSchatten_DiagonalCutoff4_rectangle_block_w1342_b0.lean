-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1342_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:13.818349+00:00
-- url     : https://prove2.me/submissions/83e43e19-3ffc-49fd-8f57-057d2e332fd6

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
theorem support_rectangle_w1342_s0_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1809146243/10000000000 : ℝ)*x 0 + (5996916691/10000000000 : ℝ)*x 1 + (2405454543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1809146243/10000000000 : ℝ)^2151 ≤ (2121041363063/20000000000000 : ℝ)^1639 := by
    have hnat : (1809146243 : ℕ)^2151*20000000000000^1639 ≤ 2121041363063^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809146243 10000000000 2121041363063 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5996916691/10000000000 : ℝ)^2151 ≤ (25557944912357/50000000000000 : ℝ)^1639 := by
    have hnat : (5996916691 : ℕ)^2151*50000000000000^1639 ≤ 25557944912357^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996916691 10000000000 25557944912357 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405454543/5000000000 : ℝ)^2151 ≤ (19139451673217/50000000000000 : ℝ)^1639 := by
    have hnat : (2405454543 : ℕ)^2151*50000000000000^1639 ≤ 19139451673217^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405454543 5000000000 19139451673217 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1809146243/10000000000 : ℝ), (5996916691/10000000000 : ℝ), (2405454543/5000000000 : ℝ)] ![(2121041363063/20000000000000 : ℝ), (25557944912357/50000000000000 : ℝ), (19139451673217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1809146243/10000000000 : ℝ)|^2151 ≤ (2121041363063/20000000000000 : ℝ)^1639
        have hw : |(-1809146243/10000000000 : ℝ)|=(1809146243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5996916691/10000000000 : ℝ)|^2151 ≤ (25557944912357/50000000000000 : ℝ)^1639
        have hw : |(5996916691/10000000000 : ℝ)|=(5996916691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405454543/5000000000 : ℝ)|^2151 ≤ (19139451673217/50000000000000 : ℝ)^1639
        have hw : |(2405454543/5000000000 : ℝ)|=(2405454543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5501812603/10000000000 : ℝ)*x 0 + (-620816879/2500000000 : ℝ)*x 1 + (2405454747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501812603/10000000000 : ℝ)^2151 ≤ (45650289944903/100000000000000 : ℝ)^1639 := by
    have hnat : (5501812603 : ℕ)^2151*100000000000000^1639 ≤ 45650289944903^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501812603 10000000000 45650289944903 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620816879/2500000000 : ℝ)^2151 ≤ (16070802440461/100000000000000 : ℝ)^1639 := by
    have hnat : (620816879 : ℕ)^2151*100000000000000^1639 ≤ 16070802440461^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620816879 2500000000 16070802440461 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405454747/5000000000 : ℝ)^2151 ≤ (38278907606869/100000000000000 : ℝ)^1639 := by
    have hnat : (2405454747 : ℕ)^2151*100000000000000^1639 ≤ 38278907606869^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405454747 5000000000 38278907606869 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501812603/10000000000 : ℝ), (-620816879/2500000000 : ℝ), (2405454747/5000000000 : ℝ)] ![(45650289944903/100000000000000 : ℝ), (16070802440461/100000000000000 : ℝ), (38278907606869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501812603/10000000000 : ℝ)|^2151 ≤ (45650289944903/100000000000000 : ℝ)^1639
        have hw : |(5501812603/10000000000 : ℝ)|=(5501812603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620816879/2500000000 : ℝ)|^2151 ≤ (16070802440461/100000000000000 : ℝ)^1639
        have hw : |(-620816879/2500000000 : ℝ)|=(620816879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405454747/5000000000 : ℝ)|^2151 ≤ (38278907606869/100000000000000 : ℝ)^1639
        have hw : |(2405454747/5000000000 : ℝ)|=(2405454747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5501812299/10000000000 : ℝ)*x 0 + (4810909299/10000000000 : ℝ)*x 1 + (-496653629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501812299/10000000000 : ℝ)^2151 ≤ (22825143317281/50000000000000 : ℝ)^1639 := by
    have hnat : (5501812299 : ℕ)^2151*50000000000000^1639 ≤ 22825143317281^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501812299 10000000000 22825143317281 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810909299/10000000000 : ℝ)^2151 ≤ (4784863196329/12500000000000 : ℝ)^1639 := by
    have hnat : (4810909299 : ℕ)^2151*12500000000000^1639 ≤ 4784863196329^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810909299 10000000000 4784863196329 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496653629/2000000000 : ℝ)^2151 ≤ (3214161556547/20000000000000 : ℝ)^1639 := by
    have hnat : (496653629 : ℕ)^2151*20000000000000^1639 ≤ 3214161556547^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496653629 2000000000 3214161556547 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501812299/10000000000 : ℝ), (4810909299/10000000000 : ℝ), (-496653629/2000000000 : ℝ)] ![(22825143317281/50000000000000 : ℝ), (4784863196329/12500000000000 : ℝ), (3214161556547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501812299/10000000000 : ℝ)|^2151 ≤ (22825143317281/50000000000000 : ℝ)^1639
        have hw : |(5501812299/10000000000 : ℝ)|=(5501812299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810909299/10000000000 : ℝ)|^2151 ≤ (4784863196329/12500000000000 : ℝ)^1639
        have hw : |(4810909299/10000000000 : ℝ)|=(4810909299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496653629/2000000000 : ℝ)|^2151 ≤ (3214161556547/20000000000000 : ℝ)^1639
        have hw : |(-496653629/2000000000 : ℝ)|=(496653629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2089373349/5000000000 : ℝ)*x 0 + (388320687/1250000000 : ℝ)*x 1 + (2795371663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089373349/5000000000 : ℝ)^2151 ≤ (31817517225079/100000000000000 : ℝ)^1639 := by
    have hnat : (2089373349 : ℕ)^2151*100000000000000^1639 ≤ 31817517225079^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089373349 5000000000 31817517225079 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388320687/1250000000 : ℝ)^2151 ≤ (2695170662801/12500000000000 : ℝ)^1639 := by
    have hnat : (388320687 : ℕ)^2151*12500000000000^1639 ≤ 2695170662801^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388320687 1250000000 2695170662801 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2795371663/5000000000 : ℝ)^2151 ≤ (46621117459573/100000000000000 : ℝ)^1639 := by
    have hnat : (2795371663 : ℕ)^2151*100000000000000^1639 ≤ 46621117459573^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795371663 5000000000 46621117459573 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089373349/5000000000 : ℝ), (388320687/1250000000 : ℝ), (2795371663/5000000000 : ℝ)] ![(31817517225079/100000000000000 : ℝ), (2695170662801/12500000000000 : ℝ), (46621117459573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089373349/5000000000 : ℝ)|^2151 ≤ (31817517225079/100000000000000 : ℝ)^1639
        have hw : |(2089373349/5000000000 : ℝ)|=(2089373349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388320687/1250000000 : ℝ)|^2151 ≤ (2695170662801/12500000000000 : ℝ)^1639
        have hw : |(388320687/1250000000 : ℝ)|=(388320687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2795371663/5000000000 : ℝ)|^2151 ≤ (46621117459573/100000000000000 : ℝ)^1639
        have hw : |(2795371663/5000000000 : ℝ)|=(2795371663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813602829/10000000000 : ℝ)*x 0 + (4841434183/10000000000 : ℝ)*x 1 + (1491325449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813602829/10000000000 : ℝ)^2151 ≤ (2127901079831/20000000000000 : ℝ)^1639 := by
    have hnat : (1813602829 : ℕ)^2151*20000000000000^1639 ≤ 2127901079831^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813602829 10000000000 2127901079831 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4841434183/10000000000 : ℝ)^2151 ≤ (3859796926203/10000000000000 : ℝ)^1639 := by
    have hnat : (4841434183 : ℕ)^2151*10000000000000^1639 ≤ 3859796926203^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4841434183 10000000000 3859796926203 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1491325449/2500000000 : ℝ)^2151 ≤ (25381262661079/50000000000000 : ℝ)^1639 := by
    have hnat : (1491325449 : ℕ)^2151*50000000000000^1639 ≤ 25381262661079^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491325449 2500000000 25381262661079 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813602829/10000000000 : ℝ), (4841434183/10000000000 : ℝ), (1491325449/2500000000 : ℝ)] ![(2127901079831/20000000000000 : ℝ), (3859796926203/10000000000000 : ℝ), (25381262661079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813602829/10000000000 : ℝ)|^2151 ≤ (2127901079831/20000000000000 : ℝ)^1639
        have hw : |(-1813602829/10000000000 : ℝ)|=(1813602829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4841434183/10000000000 : ℝ)|^2151 ≤ (3859796926203/10000000000000 : ℝ)^1639
        have hw : |(4841434183/10000000000 : ℝ)|=(4841434183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1491325449/2500000000 : ℝ)|^2151 ≤ (25381262661079/50000000000000 : ℝ)^1639
        have hw : |(1491325449/2500000000 : ℝ)|=(1491325449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5178586769/10000000000 : ℝ)*x 0 + (-664438089/5000000000 : ℝ)*x 1 + (5965301569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178586769/10000000000 : ℝ)^2151 ≤ (42163336384809/100000000000000 : ℝ)^1639 := by
    have hnat : (5178586769 : ℕ)^2151*100000000000000^1639 ≤ 42163336384809^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178586769 10000000000 42163336384809 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (664438089/5000000000 : ℝ)^2151 ≤ (7074140806851/100000000000000 : ℝ)^1639 := by
    have hnat : (664438089 : ℕ)^2151*100000000000000^1639 ≤ 7074140806851^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664438089 5000000000 7074140806851 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5965301569/10000000000 : ℝ)^2151 ≤ (317265767419/625000000000 : ℝ)^1639 := by
    have hnat : (5965301569 : ℕ)^2151*625000000000^1639 ≤ 317265767419^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965301569 10000000000 317265767419 625000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178586769/10000000000 : ℝ), (-664438089/5000000000 : ℝ), (5965301569/10000000000 : ℝ)] ![(42163336384809/100000000000000 : ℝ), (7074140806851/100000000000000 : ℝ), (317265767419/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178586769/10000000000 : ℝ)|^2151 ≤ (42163336384809/100000000000000 : ℝ)^1639
        have hw : |(5178586769/10000000000 : ℝ)|=(5178586769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-664438089/5000000000 : ℝ)|^2151 ≤ (7074140806851/100000000000000 : ℝ)^1639
        have hw : |(-664438089/5000000000 : ℝ)|=(664438089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5965301569/10000000000 : ℝ)|^2151 ≤ (317265767419/625000000000 : ℝ)^1639
        have hw : |(5965301569/10000000000 : ℝ)|=(5965301569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5178586759/10000000000 : ℝ)*x 0 + (5965301797/10000000000 : ℝ)*x 1 + (-1328875831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178586759/10000000000 : ℝ)^2151 ≤ (10540834069489/25000000000000 : ℝ)^1639 := by
    have hnat : (5178586759 : ℕ)^2151*25000000000000^1639 ≤ 10540834069489^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178586759 10000000000 10540834069489 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5965301797/10000000000 : ℝ)^2151 ≤ (25381262666663/50000000000000 : ℝ)^1639 := by
    have hnat : (5965301797 : ℕ)^2151*50000000000000^1639 ≤ 25381262666663^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965301797 10000000000 25381262666663 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328875831/10000000000 : ℝ)^2151 ≤ (3537069191293/50000000000000 : ℝ)^1639 := by
    have hnat : (1328875831 : ℕ)^2151*50000000000000^1639 ≤ 3537069191293^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328875831 10000000000 3537069191293 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178586759/10000000000 : ℝ), (5965301797/10000000000 : ℝ), (-1328875831/10000000000 : ℝ)] ![(10540834069489/25000000000000 : ℝ), (25381262666663/50000000000000 : ℝ), (3537069191293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178586759/10000000000 : ℝ)|^2151 ≤ (10540834069489/25000000000000 : ℝ)^1639
        have hw : |(5178586759/10000000000 : ℝ)|=(5178586759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5965301797/10000000000 : ℝ)|^2151 ≤ (25381262666663/50000000000000 : ℝ)^1639
        have hw : |(5965301797/10000000000 : ℝ)|=(5965301797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1328875831/10000000000 : ℝ)|^2151 ≤ (3537069191293/50000000000000 : ℝ)^1639
        have hw : |(-1328875831/10000000000 : ℝ)|=(1328875831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s0_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (418807949/1000000000 : ℝ)*x 0 + (5526807201/10000000000 : ℝ)*x 1 + (1586392289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418807949/1000000000 : ℝ)^2151 ≤ (31910809284583/100000000000000 : ℝ)^1639 := by
    have hnat : (418807949 : ℕ)^2151*100000000000000^1639 ≤ 31910809284583^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418807949 1000000000 31910809284583 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526807201/10000000000 : ℝ)^2151 ≤ (11480664018217/25000000000000 : ℝ)^1639 := by
    have hnat : (5526807201 : ℕ)^2151*25000000000000^1639 ≤ 11480664018217^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526807201 10000000000 11480664018217 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586392289/5000000000 : ℝ)^2151 ≤ (5541633657519/25000000000000 : ℝ)^1639 := by
    have hnat : (1586392289 : ℕ)^2151*25000000000000^1639 ≤ 5541633657519^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586392289 5000000000 5541633657519 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418807949/1000000000 : ℝ), (5526807201/10000000000 : ℝ), (1586392289/5000000000 : ℝ)] ![(31910809284583/100000000000000 : ℝ), (11480664018217/25000000000000 : ℝ), (5541633657519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418807949/1000000000 : ℝ)|^2151 ≤ (31910809284583/100000000000000 : ℝ)^1639
        have hw : |(418807949/1000000000 : ℝ)|=(418807949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526807201/10000000000 : ℝ)|^2151 ≤ (11480664018217/25000000000000 : ℝ)^1639
        have hw : |(5526807201/10000000000 : ℝ)|=(5526807201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586392289/5000000000 : ℝ)|^2151 ≤ (5541633657519/25000000000000 : ℝ)^1639
        have hw : |(1586392289/5000000000 : ℝ)|=(1586392289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (707/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26871/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4301/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4301 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4301*1^1024 ≤ 0^1024*1^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4301/1024 : ℝ) ≤ (2130954814683862243/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4301 ≤ (2130954814683862243/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4301*100000000000000000000^1024 ≤ 2130954814683862243^1024*5^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2130954814683862243 100000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2130954814683862243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4301 := by
      have hnat : (1 : ℕ)^1024*1^4301 ≤ 1^4301*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102130954814683862243/100000000000000000000 : ℝ) ≤ (40201311495891/40000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (102130954814683862243/100000000000000000000 : ℝ)^1024 ≤ (40201311495891/40000000000000 : ℝ)^4301 := by
      have hnat : (102130954814683862243 : ℕ)^1024*40000000000000^4301 ≤ 40201311495891^4301*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102130954814683862243 100000000000000000000 40201311495891 40000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40201311495891/40000000000000 : ℝ)) (X := (102130954814683862243/100000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52130954814683862243/50000000000000000000 : ℝ) ≤ (20201311495891/20000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (52130954814683862243/50000000000000000000 : ℝ)^1024 ≤ (20201311495891/20000000000000 : ℝ)^4301 := by
      have hnat : (52130954814683862243 : ℕ)^1024*20000000000000^4301 ≤ 20201311495891^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52130954814683862243 50000000000000000000 20201311495891 20000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20201311495891/20000000000000 : ℝ)) (X := (52130954814683862243/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(201311495891/16000000000000 : ℝ)*(0 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(201311495891/16000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2130954814683862243/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(201311495891/16000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (1 : ℝ)+(201311495891/16000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(40201311495891/40000000000000 : ℝ) by norm_num, show 1+(2130954814683862243/100000000000000000000 : ℝ)+(0 : ℝ)=(102130954814683862243/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2130954814683862243/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(201311495891/16000000000000 : ℝ)*(2/5 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(201311495891/16000000000000 : ℝ)*(2/5 : ℝ)=(20201311495891/20000000000000 : ℝ) by norm_num, show 1+2*(2130954814683862243/100000000000000000000 : ℝ)=(52130954814683862243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(201311495891/16000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (201311495891/16000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(201311495891/16000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (201311495891/16000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(201311495891/16000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (201311495891/16000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1809146243/10000000000 : ℝ)*X 0 0+(5996916691/10000000000 : ℝ)*X 0 1+(2405454543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5501812603/10000000000 : ℝ)*X 1 0+(-620816879/2500000000 : ℝ)*X 1 1+(2405454747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5501812299/10000000000 : ℝ)*X 2 0+(4810909299/10000000000 : ℝ)*X 2 1+(-496653629/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089373349/5000000000 : ℝ)*X 0 0+(388320687/1250000000 : ℝ)*X 0 1+(2795371663/5000000000 : ℝ)*X 0 2+(2089373349/5000000000 : ℝ)*X 1 0+(388320687/1250000000 : ℝ)*X 1 1+(2795371663/5000000000 : ℝ)*X 1 2+(2089373349/5000000000 : ℝ)*X 2 0+(388320687/1250000000 : ℝ)*X 2 1+(2795371663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1813602829/10000000000 : ℝ)*X 0 0+(4841434183/10000000000 : ℝ)*X 0 1+(1491325449/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5178586769/10000000000 : ℝ)*X 1 0+(-664438089/5000000000 : ℝ)*X 1 1+(5965301569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5178586759/10000000000 : ℝ)*X 2 0+(5965301797/10000000000 : ℝ)*X 2 1+(-1328875831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418807949/1000000000 : ℝ)*X 0 0+(5526807201/10000000000 : ℝ)*X 0 1+(1586392289/5000000000 : ℝ)*X 0 2+(418807949/1000000000 : ℝ)*X 1 0+(5526807201/10000000000 : ℝ)*X 1 1+(1586392289/5000000000 : ℝ)*X 1 2+(418807949/1000000000 : ℝ)*X 2 0+(5526807201/10000000000 : ℝ)*X 2 1+(1586392289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6320319293762492817/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114464373/100000000000000 : ℝ)*(base1) + (753151897/50000000000000 : ℝ)*(base19) + (1459714669/100000000000000 : ℝ)*(base23) + (247572337/100000000000000 : ℝ)*(upper3) + (72201819/100000000000000 : ℝ)*(upper5) + (155715880278123/25000000000000 : ℝ)*(major0) + (155715880278123/25000000000000 : ℝ)*(major1) + (155715880278123/25000000000000 : ℝ)*(major2) + (421585132136259/50000000000000 : ℝ)*(sp0) + (421586545415253/50000000000000 : ℝ)*(sp1) + (843173137419631/100000000000000 : ℝ)*(sp2) + (402549606730923/100000000000000 : ℝ)*(sp3) + (889465231/20000000000000 : ℝ)*(sp4) + (314152259/12500000000000 : ℝ)*(sp7) + (50319029301671/12500000000000 : ℝ)*(f.failure) + (8431745971343/1000000000000 : ℝ)*(f.sum) + (201696940407/200000000000000000000000000 : ℝ)*base66 + (1328362259393/400000000000000000000000000 : ℝ)*base67 + (3094997115793/400000000000000000000000000 : ℝ)*base69 + (2426670631793/400000000000000000000000000 : ℝ)*base71 + (1143613544207/200000000000000000000000000 : ℝ)*base74 + (3969136701393/400000000000000000000000000 : ℝ)*base75 + (1901800811393/400000000000000000000000000 : ℝ)*base77 + (3844644512993/400000000000000000000000000 : ℝ)*base79 + (248270111207/200000000000000000000000000 : ℝ)*base82 + (3174309/1250000000000000000000 : ℝ)*base90 + (3174309/1250000000000000000000 : ℝ)*base92 + (3174309/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (477533848437296670843/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (938891933/100000000000000 : ℝ)*(base19) + (518633737/50000000000000 : ℝ)*(base23) + (23205191/25000000000000 : ℝ)*(base39) + (56585407/50000000000000 : ℝ)*(upper3) + (35679457/25000000000000 : ℝ)*(upper5) + (657294427042001/100000000000000 : ℝ)*(major0) + (657294427042001/100000000000000 : ℝ)*(major1) + (164323583555309/25000000000000 : ℝ)*(major2) + (1063094929/50000000000000 : ℝ)*(sp1) + (2278848057/100000000000000 : ℝ)*(sp2) + (35591356786867/4000000000000 : ℝ)*(sp4) + (177956170917977/20000000000000 : ℝ)*(sp5) + (222445174094227/25000000000000 : ℝ)*(sp6) + (84960936482721/20000000000000 : ℝ)*(sp7) + (84960936482721/20000000000000 : ℝ)*(f.failure) + (22244600312311/2500000000000 : ℝ)*(f.sum) + (89226259167/1600000000000000000000000000 : ℝ)*base65 + (1920430283319/400000000000000000000000000 : ℝ)*base67 + (4007143266109/1600000000000000000000000000 : ℝ)*base70 + (464975379719/400000000000000000000000000 : ℝ)*base71 + (2406403103967/1600000000000000000000000000 : ℝ)*base73 + (9019804253309/1600000000000000000000000000 : ℝ)*base76 + (10352434853891/1600000000000000000000000000 : ℝ)*base77 + (13726867399491/1600000000000000000000000000 : ℝ)*base79 + (384747183709/800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9342259/2000000000000000000000 : ℝ)*base90 + (9342259/2000000000000000000000 : ℝ)*base92 + (10657741/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1342_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26871/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1342_s1_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-398792559/2000000000 : ℝ)*x 0 + (2821066433/5000000000 : ℝ)*x 1 + (252366729/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398792559/2000000000 : ℝ)^2151 ≤ (12049214635377/100000000000000 : ℝ)^1639 := by
    have hnat : (398792559 : ℕ)^2151*100000000000000^1639 ≤ 12049214635377^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398792559 2000000000 12049214635377 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2821066433/5000000000 : ℝ)^2151 ≤ (23592164197259/50000000000000 : ℝ)^1639 := by
    have hnat : (2821066433 : ℕ)^2151*50000000000000^1639 ≤ 23592164197259^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821066433 5000000000 23592164197259 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252366729/500000000 : ℝ)^2151 ≤ (5095807120399/12500000000000 : ℝ)^1639 := by
    have hnat : (252366729 : ℕ)^2151*12500000000000^1639 ≤ 5095807120399^1639*500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252366729 500000000 5095807120399 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398792559/2000000000 : ℝ), (2821066433/5000000000 : ℝ), (252366729/500000000 : ℝ)] ![(12049214635377/100000000000000 : ℝ), (23592164197259/50000000000000 : ℝ), (5095807120399/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398792559/2000000000 : ℝ)|^2151 ≤ (12049214635377/100000000000000 : ℝ)^1639
        have hw : |(-398792559/2000000000 : ℝ)|=(398792559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2821066433/5000000000 : ℝ)|^2151 ≤ (23592164197259/50000000000000 : ℝ)^1639
        have hw : |(2821066433/5000000000 : ℝ)|=(2821066433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252366729/500000000 : ℝ)|^2151 ≤ (5095807120399/12500000000000 : ℝ)^1639
        have hw : |(252366729/500000000 : ℝ)|=(252366729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5405717081/10000000000 : ℝ)*x 0 + (-144460069/625000000 : ℝ)*x 1 + (1261833647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405717081/10000000000 : ℝ)^2151 ≤ (11151686255531/25000000000000 : ℝ)^1639 := by
    have hnat : (5405717081 : ℕ)^2151*25000000000000^1639 ≤ 11151686255531^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405717081 10000000000 11151686255531 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144460069/625000000 : ℝ)^2151 ≤ (14626797915871/100000000000000 : ℝ)^1639 := by
    have hnat : (144460069 : ℕ)^2151*100000000000000^1639 ≤ 14626797915871^1639*625000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144460069 625000000 14626797915871 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1261833647/2500000000 : ℝ)^2151 ≤ (40766457047991/100000000000000 : ℝ)^1639 := by
    have hnat : (1261833647 : ℕ)^2151*100000000000000^1639 ≤ 40766457047991^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261833647 2500000000 40766457047991 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405717081/10000000000 : ℝ), (-144460069/625000000 : ℝ), (1261833647/2500000000 : ℝ)] ![(11151686255531/25000000000000 : ℝ), (14626797915871/100000000000000 : ℝ), (40766457047991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405717081/10000000000 : ℝ)|^2151 ≤ (11151686255531/25000000000000 : ℝ)^1639
        have hw : |(5405717081/10000000000 : ℝ)|=(5405717081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144460069/625000000 : ℝ)|^2151 ≤ (14626797915871/100000000000000 : ℝ)^1639
        have hw : |(-144460069/625000000 : ℝ)|=(144460069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1261833647/2500000000 : ℝ)|^2151 ≤ (40766457047991/100000000000000 : ℝ)^1639
        have hw : |(1261833647/2500000000 : ℝ)|=(1261833647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081143413/2000000000 : ℝ)*x 0 + (126183359/250000000 : ℝ)*x 1 + (-288920177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081143413/2000000000 : ℝ)^2151 ≤ (44606744848851/100000000000000 : ℝ)^1639 := by
    have hnat : (1081143413 : ℕ)^2151*100000000000000^1639 ≤ 44606744848851^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081143413 2000000000 44606744848851 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126183359/250000000 : ℝ)^2151 ≤ (40766454631211/100000000000000 : ℝ)^1639 := by
    have hnat : (126183359 : ℕ)^2151*100000000000000^1639 ≤ 40766454631211^1639*250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126183359 250000000 40766454631211 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (288920177/1250000000 : ℝ)^2151 ≤ (292536010141/2000000000000 : ℝ)^1639 := by
    have hnat : (288920177 : ℕ)^2151*2000000000000^1639 ≤ 292536010141^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288920177 1250000000 292536010141 2000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081143413/2000000000 : ℝ), (126183359/250000000 : ℝ), (-288920177/1250000000 : ℝ)] ![(44606744848851/100000000000000 : ℝ), (40766454631211/100000000000000 : ℝ), (292536010141/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081143413/2000000000 : ℝ)|^2151 ≤ (44606744848851/100000000000000 : ℝ)^1639
        have hw : |(1081143413/2000000000 : ℝ)|=(1081143413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126183359/250000000 : ℝ)|^2151 ≤ (40766454631211/100000000000000 : ℝ)^1639
        have hw : |(126183359/250000000 : ℝ)|=(126183359/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-288920177/1250000000 : ℝ)|^2151 ≤ (292536010141/2000000000000 : ℝ)^1639
        have hw : |(-288920177/1250000000 : ℝ)|=(288920177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (858461599/2000000000 : ℝ)*x 0 + (1855636769/5000000000 : ℝ)*x 1 + (2478560601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858461599/2000000000 : ℝ)^2151 ≤ (32957085312223/100000000000000 : ℝ)^1639 := by
    have hnat : (858461599 : ℕ)^2151*100000000000000^1639 ≤ 32957085312223^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858461599 2000000000 32957085312223 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1855636769/5000000000 : ℝ)^2151 ≤ (1089201245021/4000000000000 : ℝ)^1639 := by
    have hnat : (1855636769 : ℕ)^2151*4000000000000^1639 ≤ 1089201245021^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855636769 5000000000 1089201245021 4000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2478560601/5000000000 : ℝ)^2151 ≤ (398128835399/1000000000000 : ℝ)^1639 := by
    have hnat : (2478560601 : ℕ)^2151*1000000000000^1639 ≤ 398128835399^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478560601 5000000000 398128835399 1000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858461599/2000000000 : ℝ), (1855636769/5000000000 : ℝ), (2478560601/5000000000 : ℝ)] ![(32957085312223/100000000000000 : ℝ), (1089201245021/4000000000000 : ℝ), (398128835399/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858461599/2000000000 : ℝ)|^2151 ≤ (32957085312223/100000000000000 : ℝ)^1639
        have hw : |(858461599/2000000000 : ℝ)|=(858461599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1855636769/5000000000 : ℝ)|^2151 ≤ (1089201245021/4000000000000 : ℝ)^1639
        have hw : |(1855636769/5000000000 : ℝ)|=(1855636769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2478560601/5000000000 : ℝ)|^2151 ≤ (398128835399/1000000000000 : ℝ)^1639
        have hw : |(2478560601/5000000000 : ℝ)|=(2478560601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-249312403/1250000000 : ℝ)*x 0 + (2527398481/5000000000 : ℝ)*x 1 + (5634534817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249312403/1250000000 : ℝ)^2151 ≤ (12053468989557/100000000000000 : ℝ)^1639 := by
    have hnat : (249312403 : ℕ)^2151*100000000000000^1639 ≤ 12053468989557^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249312403 1250000000 12053468989557 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527398481/5000000000 : ℝ)^2151 ≤ (10211393957243/25000000000000 : ℝ)^1639 := by
    have hnat : (2527398481 : ℕ)^2151*25000000000000^1639 ≤ 10211393957243^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527398481 5000000000 10211393957243 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634534817/10000000000 : ℝ)^2151 ≤ (47100955164203/100000000000000 : ℝ)^1639 := by
    have hnat : (5634534817 : ℕ)^2151*100000000000000^1639 ≤ 47100955164203^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634534817 10000000000 47100955164203 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249312403/1250000000 : ℝ), (2527398481/5000000000 : ℝ), (5634534817/10000000000 : ℝ)] ![(12053468989557/100000000000000 : ℝ), (10211393957243/25000000000000 : ℝ), (47100955164203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249312403/1250000000 : ℝ)|^2151 ≤ (12053468989557/100000000000000 : ℝ)^1639
        have hw : |(-249312403/1250000000 : ℝ)|=(249312403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527398481/5000000000 : ℝ)|^2151 ≤ (10211393957243/25000000000000 : ℝ)^1639
        have hw : |(2527398481/5000000000 : ℝ)|=(2527398481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634534817/10000000000 : ℝ)|^2151 ≤ (47100955164203/100000000000000 : ℝ)^1639
        have hw : |(5634534817/10000000000 : ℝ)|=(5634534817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5251375163/10000000000 : ℝ)*x 0 + (-1724161519/10000000000 : ℝ)*x 1 + (5634534007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251375163/10000000000 : ℝ)^2151 ≤ (10735700364687/25000000000000 : ℝ)^1639 := by
    have hnat : (5251375163 : ℕ)^2151*25000000000000^1639 ≤ 10735700364687^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251375163 10000000000 10735700364687 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724161519/10000000000 : ℝ)^2151 ≤ (1991250450829/20000000000000 : ℝ)^1639 := by
    have hnat : (1724161519 : ℕ)^2151*20000000000000^1639 ≤ 1991250450829^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724161519 10000000000 1991250450829 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634534007/10000000000 : ℝ)^2151 ≤ (47100946277961/100000000000000 : ℝ)^1639 := by
    have hnat : (5634534007 : ℕ)^2151*100000000000000^1639 ≤ 47100946277961^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634534007 10000000000 47100946277961 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251375163/10000000000 : ℝ), (-1724161519/10000000000 : ℝ), (5634534007/10000000000 : ℝ)] ![(10735700364687/25000000000000 : ℝ), (1991250450829/20000000000000 : ℝ), (47100946277961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251375163/10000000000 : ℝ)|^2151 ≤ (10735700364687/25000000000000 : ℝ)^1639
        have hw : |(5251375163/10000000000 : ℝ)|=(5251375163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724161519/10000000000 : ℝ)|^2151 ≤ (1991250450829/20000000000000 : ℝ)^1639
        have hw : |(-1724161519/10000000000 : ℝ)|=(1724161519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634534007/10000000000 : ℝ)|^2151 ≤ (47100946277961/100000000000000 : ℝ)^1639
        have hw : |(5634534007/10000000000 : ℝ)|=(5634534007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1050274881/2000000000 : ℝ)*x 0 + (2817266901/5000000000 : ℝ)*x 1 + (-1724162887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050274881/2000000000 : ℝ)^2151 ≤ (42942793323927/100000000000000 : ℝ)^1639 := by
    have hnat : (1050274881 : ℕ)^2151*100000000000000^1639 ≤ 42942793323927^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050274881 2000000000 42942793323927 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2817266901/5000000000 : ℝ)^2151 ≤ (23550472014487/50000000000000 : ℝ)^1639 := by
    have hnat : (2817266901 : ℕ)^2151*50000000000000^1639 ≤ 23550472014487^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817266901 5000000000 23550472014487 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724162887/10000000000 : ℝ)^2151 ≤ (4978131310721/50000000000000 : ℝ)^1639 := by
    have hnat : (1724162887 : ℕ)^2151*50000000000000^1639 ≤ 4978131310721^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724162887 10000000000 4978131310721 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050274881/2000000000 : ℝ), (2817266901/5000000000 : ℝ), (-1724162887/10000000000 : ℝ)] ![(42942793323927/100000000000000 : ℝ), (23550472014487/50000000000000 : ℝ), (4978131310721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050274881/2000000000 : ℝ)|^2151 ≤ (42942793323927/100000000000000 : ℝ)^1639
        have hw : |(1050274881/2000000000 : ℝ)|=(1050274881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2817266901/5000000000 : ℝ)|^2151 ≤ (23550472014487/50000000000000 : ℝ)^1639
        have hw : |(2817266901/5000000000 : ℝ)|=(2817266901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1724162887/10000000000 : ℝ)|^2151 ≤ (4978131310721/50000000000000 : ℝ)^1639
        have hw : |(-1724162887/10000000000 : ℝ)|=(1724162887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s1_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4293430843/10000000000 : ℝ)*x 0 + (4941489841/10000000000 : ℝ)*x 1 + (1863594991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293430843/10000000000 : ℝ)^2151 ≤ (16484200202107/50000000000000 : ℝ)^1639 := by
    have hnat : (4293430843 : ℕ)^2151*50000000000000^1639 ≤ 16484200202107^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293430843 10000000000 16484200202107 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4941489841/10000000000 : ℝ)^2151 ≤ (39648204533743/100000000000000 : ℝ)^1639 := by
    have hnat : (4941489841 : ℕ)^2151*100000000000000^1639 ≤ 39648204533743^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4941489841 10000000000 39648204533743 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863594991/5000000000 : ℝ)^2151 ≤ (27383395048483/100000000000000 : ℝ)^1639 := by
    have hnat : (1863594991 : ℕ)^2151*100000000000000^1639 ≤ 27383395048483^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863594991 5000000000 27383395048483 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293430843/10000000000 : ℝ), (4941489841/10000000000 : ℝ), (1863594991/5000000000 : ℝ)] ![(16484200202107/50000000000000 : ℝ), (39648204533743/100000000000000 : ℝ), (27383395048483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293430843/10000000000 : ℝ)|^2151 ≤ (16484200202107/50000000000000 : ℝ)^1639
        have hw : |(4293430843/10000000000 : ℝ)|=(4293430843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4941489841/10000000000 : ℝ)|^2151 ≤ (39648204533743/100000000000000 : ℝ)^1639
        have hw : |(4941489841/10000000000 : ℝ)|=(4941489841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1863594991/5000000000 : ℝ)|^2151 ≤ (27383395048483/100000000000000 : ℝ)^1639
        have hw : |(1863594991/5000000000 : ℝ)|=(1863594991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (689/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19461/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26871/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26871/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26871/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26871/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26871/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26871/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (707/50000 : ℝ) ^ (4301/1024 : ℝ) ≤ (852111219793/50000000000000000000 : ℝ) := by
    have hpowers : (707/50000 : ℝ)^4301 ≤ (852111219793/50000000000000000000 : ℝ)^1024 := by
      have hnat : (707 : ℕ)^4301*50000000000000000000^1024 ≤ 852111219793^1024*50000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 50000 852111219793 50000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/50000 : ℝ)) (X := (852111219793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26871/100000 : ℝ) ^ (4301/1024 : ℝ) ≤ (200378267751636067/50000000000000000000 : ℝ) := by
    have hpowers : (26871/100000 : ℝ)^4301 ≤ (200378267751636067/50000000000000000000 : ℝ)^1024 := by
      have hnat : (26871 : ℕ)^4301*50000000000000000000^1024 ≤ 200378267751636067^1024*100000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26871 100000 200378267751636067 50000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26871/100000 : ℝ)) (X := (200378267751636067/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000852111219793/25000000000000000000 : ℝ) ≤ (400000003245987/400000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (25000000852111219793/25000000000000000000 : ℝ)^1024 ≤ (400000003245987/400000000000000 : ℝ)^4301 := by
      have hnat : (25000000852111219793 : ℕ)^1024*400000000000000^4301 ≤ 400000003245987^4301*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000852111219793 25000000000000000000 400000003245987 400000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000003245987/400000000000000 : ℝ)) (X := (25000000852111219793/25000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2510018955993142793/2500000000000000000 : ℝ) ≤ (200190537725201/200000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (2510018955993142793/2500000000000000000 : ℝ)^1024 ≤ (200190537725201/200000000000000 : ℝ)^4301 := by
      have hnat : (2510018955993142793 : ℕ)^1024*200000000000000^4301 ≤ 200190537725201^4301*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2510018955993142793 2500000000000000000 200190537725201 200000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200190537725201/200000000000000 : ℝ)) (X := (2510018955993142793/2500000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25200378267751636067/25000000000000000000 : ℝ) ≤ (400762147654817/400000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (25200378267751636067/25000000000000000000 : ℝ)^1024 ≤ (400762147654817/400000000000000 : ℝ)^4301 := by
      have hnat : (25200378267751636067 : ℕ)^1024*400000000000000^4301 ≤ 400762147654817^4301*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25200378267751636067 25000000000000000000 400762147654817 400000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400762147654817/400000000000000 : ℝ)) (X := (25200378267751636067/25000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(852111219793/50000000000000000000 : ℝ) ≤ ((10181722410439005439/10182800000000000000 : ℝ)+2*(76214440883/20365600000000 : ℝ)*(707/50000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (10181722410439005439/10182800000000000000 : ℝ)+2*(76214440883/20365600000000 : ℝ)*(707/50000 : ℝ)=(400000003245987/400000000000000 : ℝ) by norm_num, show 1+2*(852111219793/50000000000000000000 : ℝ)=(25000000852111219793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(200378267751636067/50000000000000000000 : ℝ)+(852111219793/50000000000000000000 : ℝ) ≤ ((10181722410439005439/10182800000000000000 : ℝ)+(76214440883/20365600000000 : ℝ)*((26871/100000 : ℝ)+(707/50000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (10181722410439005439/10182800000000000000 : ℝ)+(76214440883/20365600000000 : ℝ)*((26871/100000 : ℝ)+(707/50000 : ℝ))=(200190537725201/200000000000000 : ℝ) by norm_num, show 1+(200378267751636067/50000000000000000000 : ℝ)+(852111219793/50000000000000000000 : ℝ)=(2510018955993142793/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(200378267751636067/50000000000000000000 : ℝ) ≤ ((10181722410439005439/10182800000000000000 : ℝ)+2*(76214440883/20365600000000 : ℝ)*(26871/100000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (10181722410439005439/10182800000000000000 : ℝ)+2*(76214440883/20365600000000 : ℝ)*(26871/100000 : ℝ)=(400762147654817/400000000000000 : ℝ) by norm_num, show 1+2*(200378267751636067/50000000000000000000 : ℝ)=(25200378267751636067/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10181722410439005439/10182800000000000000 : ℝ)*(X 1 0+X 2 0)+(76214440883/20365600000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (707/50000 : ℝ)) (hi := (26871/100000 : ℝ)) (c := (10181722410439005439/10182800000000000000 : ℝ)) (alpha := (76214440883/20365600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10181722410439005439/10182800000000000000 : ℝ)*(X 0 1+X 2 1)+(76214440883/20365600000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (707/50000 : ℝ)) (hi := (26871/100000 : ℝ)) (c := (10181722410439005439/10182800000000000000 : ℝ)) (alpha := (76214440883/20365600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10181722410439005439/10182800000000000000 : ℝ)*(X 0 2+X 1 2)+(76214440883/20365600000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (707/50000 : ℝ)) (hi := (26871/100000 : ℝ)) (c := (10181722410439005439/10182800000000000000 : ℝ)) (alpha := (76214440883/20365600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398792559/2000000000 : ℝ)*X 0 0+(2821066433/5000000000 : ℝ)*X 0 1+(252366729/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5405717081/10000000000 : ℝ)*X 1 0+(-144460069/625000000 : ℝ)*X 1 1+(1261833647/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1081143413/2000000000 : ℝ)*X 2 0+(126183359/250000000 : ℝ)*X 2 1+(-288920177/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((858461599/2000000000 : ℝ)*X 0 0+(1855636769/5000000000 : ℝ)*X 0 1+(2478560601/5000000000 : ℝ)*X 0 2+(858461599/2000000000 : ℝ)*X 1 0+(1855636769/5000000000 : ℝ)*X 1 1+(2478560601/5000000000 : ℝ)*X 1 2+(858461599/2000000000 : ℝ)*X 2 0+(1855636769/5000000000 : ℝ)*X 2 1+(2478560601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-249312403/1250000000 : ℝ)*X 0 0+(2527398481/5000000000 : ℝ)*X 0 1+(5634534817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251375163/10000000000 : ℝ)*X 1 0+(-1724161519/10000000000 : ℝ)*X 1 1+(5634534007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050274881/2000000000 : ℝ)*X 2 0+(2817266901/5000000000 : ℝ)*X 2 1+(-1724162887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4293430843/10000000000 : ℝ)*X 0 0+(4941489841/10000000000 : ℝ)*X 0 1+(1863594991/5000000000 : ℝ)*X 0 2+(4293430843/10000000000 : ℝ)*X 1 0+(4941489841/10000000000 : ℝ)*X 1 1+(1863594991/5000000000 : ℝ)*X 1 2+(4293430843/10000000000 : ℝ)*X 2 0+(4941489841/10000000000 : ℝ)*X 2 1+(1863594991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8412940812288803610129/1591062500000000000000000000 : ℝ) := by norm_num
    linear_combination (49032027/100000000000000 : ℝ)*(base1) + (1431221/195312500000 : ℝ)*(base19) + (363904471/50000000000000 : ℝ)*(base23) + (40065141/25000000000000 : ℝ)*(upper3) + (3896329/12500000000000 : ℝ)*(upper5) + (24839196037517/2000000000000 : ℝ)*(major0) + (24839196037517/2000000000000 : ℝ)*(major1) + (24839196037517/2000000000000 : ℝ)*(major2) + (210155836921601/12500000000000 : ℝ)*(sp0) + (420312241588103/25000000000000 : ℝ)*(sp1) + (840624485664311/50000000000000 : ℝ)*(sp2) + (25083365239309/3125000000000 : ℝ)*(sp3) + (190799799/6250000000000 : ℝ)*(sp4) + (199167007/10000000000000 : ℝ)*(sp7) + (160533945671997/20000000000000 : ℝ)*(f.failure) + (420312424784391/25000000000000 : ℝ)*(f.sum) + (4794147388573/6364250000000000000000000000 : ℝ)*base65 + (206715883776925037/20365600000000000000000000000000 : ℝ)*base68 + (236761349867675437/20365600000000000000000000000000 : ℝ)*base70 + (68681437122959763/20365600000000000000000000000000 : ℝ)*base71 + (23142452082789/3182125000000000000000000000 : ℝ)*base74 + (8688972723048237/20365600000000000000000000000000 : ℝ)*base76 + (71646972785754963/20365600000000000000000000000000 : ℝ)*base77 + (13925556454524563/20365600000000000000000000000000 : ℝ)*base79 + (78906878572299/12728500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (14126137/2000000000000000000000 : ℝ)*base89 + (14126137/2000000000000000000000 : ℝ)*base91 + (14126137/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2118472716557520043639100589/509140000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40172943/20000000000000 : ℝ)*(base19) + (55225599/100000000000000 : ℝ)*(upper2) + (65183641/100000000000000 : ℝ)*(upper3) + (17494577/100000000000000 : ℝ)*(lower4) + (1274223773649617/100000000000000 : ℝ)*(major0) + (1274223773649617/100000000000000 : ℝ)*(major1) + (1274223773649617/100000000000000 : ℝ)*(major2) + (5070675907/100000000000000 : ℝ)*(sp0) + (3074498889/100000000000000 : ℝ)*(sp1) + (103077657/10000000000000 : ℝ)*(sp3) + (68996825423921/4000000000000 : ℝ)*(sp4) + (215615303863791/12500000000000 : ℝ)*(sp5) + (431231426568483/25000000000000 : ℝ)*(sp6) + (823520671552579/100000000000000 : ℝ)*(sp7) + (823521702329149/100000000000000 : ℝ)*(f.failure) + (431231426568483/25000000000000 : ℝ)*(f.sum) + (248932750273301/25457000000000000000000000000 : ℝ)*base65 + (2898510806300313137/1018280000000000000000000000000000 : ℝ)*base68 + (12217898050342073137/1018280000000000000000000000000000 : ℝ)*base70 + (1036243286072833137/1018280000000000000000000000000000 : ℝ)*base72 + (8079693124987/6364250000000000000000000000 : ℝ)*base73 + (4636777857851886863/1018280000000000000000000000000000 : ℝ)*base75 + (4359312890044806863/1018280000000000000000000000000000 : ℝ)*base77 + (2677737470622873137/1018280000000000000000000000000000 : ℝ)*base80 + (50232324693263/25457000000000000000000000000 : ℝ)*base82 + (12873529/10000000000000000000000 : ℝ)*base89 + (12873529/10000000000000000000000 : ℝ)*base91 + (12873529/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1342_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (689/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19461/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1342_s2_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2034117811/10000000000 : ℝ)*x 0 + (1369935479/2500000000 : ℝ)*x 1 + (5184003989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034117811/10000000000 : ℝ)^2151 ≤ (12368662969701/100000000000000 : ℝ)^1639 := by
    have hnat : (2034117811 : ℕ)^2151*100000000000000^1639 ≤ 12368662969701^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034117811 10000000000 12368662969701 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369935479/2500000000 : ℝ)^2151 ≤ (567626334481/1250000000000 : ℝ)^1639 := by
    have hnat : (1369935479 : ℕ)^2151*1250000000000^1639 ≤ 567626334481^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369935479 2500000000 567626334481 1250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184003989/10000000000 : ℝ)^2151 ≤ (42221230254409/100000000000000 : ℝ)^1639 := by
    have hnat : (5184003989 : ℕ)^2151*100000000000000^1639 ≤ 42221230254409^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184003989 10000000000 42221230254409 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2034117811/10000000000 : ℝ), (1369935479/2500000000 : ℝ), (5184003989/10000000000 : ℝ)] ![(12368662969701/100000000000000 : ℝ), (567626334481/1250000000000 : ℝ), (42221230254409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2034117811/10000000000 : ℝ)|^2151 ≤ (12368662969701/100000000000000 : ℝ)^1639
        have hw : |(-2034117811/10000000000 : ℝ)|=(2034117811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369935479/2500000000 : ℝ)|^2151 ≤ (567626334481/1250000000000 : ℝ)^1639
        have hw : |(1369935479/2500000000 : ℝ)|=(1369935479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184003989/10000000000 : ℝ)|^2151 ≤ (42221230254409/100000000000000 : ℝ)^1639
        have hw : |(5184003989/10000000000 : ℝ)|=(5184003989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682975699/5000000000 : ℝ)*x 0 + (-109346369/500000000 : ℝ)*x 1 + (259200219/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682975699/5000000000 : ℝ)^2151 ≤ (4417659792873/10000000000000 : ℝ)^1639 := by
    have hnat : (2682975699 : ℕ)^2151*10000000000000^1639 ≤ 4417659792873^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682975699 5000000000 4417659792873 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109346369/500000000 : ℝ)^2151 ≤ (13602167618501/100000000000000 : ℝ)^1639 := by
    have hnat : (109346369 : ℕ)^2151*100000000000000^1639 ≤ 13602167618501^1639*500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109346369 500000000 13602167618501 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259200219/500000000 : ℝ)^2151 ≤ (2638827152107/6250000000000 : ℝ)^1639 := by
    have hnat : (259200219 : ℕ)^2151*6250000000000^1639 ≤ 2638827152107^1639*500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259200219 500000000 2638827152107 6250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682975699/5000000000 : ℝ), (-109346369/500000000 : ℝ), (259200219/500000000 : ℝ)] ![(4417659792873/10000000000000 : ℝ), (13602167618501/100000000000000 : ℝ), (2638827152107/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682975699/5000000000 : ℝ)|^2151 ≤ (4417659792873/10000000000000 : ℝ)^1639
        have hw : |(2682975699/5000000000 : ℝ)|=(2682975699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109346369/500000000 : ℝ)|^2151 ≤ (13602167618501/100000000000000 : ℝ)^1639
        have hw : |(-109346369/500000000 : ℝ)|=(109346369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259200219/500000000 : ℝ)|^2151 ≤ (2638827152107/6250000000000 : ℝ)^1639
        have hw : |(259200219/500000000 : ℝ)|=(259200219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5365951483/10000000000 : ℝ)*x 0 + (2592002141/5000000000 : ℝ)*x 1 + (-546731849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365951483/10000000000 : ℝ)^2151 ≤ (44176598847117/100000000000000 : ℝ)^1639 := by
    have hnat : (5365951483 : ℕ)^2151*100000000000000^1639 ≤ 44176598847117^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365951483 10000000000 44176598847117 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592002141/5000000000 : ℝ)^2151 ≤ (21110616693107/50000000000000 : ℝ)^1639 := by
    have hnat : (2592002141 : ℕ)^2151*50000000000000^1639 ≤ 21110616693107^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592002141 5000000000 21110616693107 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546731849/2500000000 : ℝ)^2151 ≤ (2720433549821/20000000000000 : ℝ)^1639 := by
    have hnat : (546731849 : ℕ)^2151*20000000000000^1639 ≤ 2720433549821^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546731849 2500000000 2720433549821 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365951483/10000000000 : ℝ), (2592002141/5000000000 : ℝ), (-546731849/2500000000 : ℝ)] ![(44176598847117/100000000000000 : ℝ), (21110616693107/50000000000000 : ℝ), (2720433549821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365951483/10000000000 : ℝ)|^2151 ≤ (44176598847117/100000000000000 : ℝ)^1639
        have hw : |(5365951483/10000000000 : ℝ)|=(5365951483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592002141/5000000000 : ℝ)|^2151 ≤ (21110616693107/50000000000000 : ℝ)^1639
        have hw : |(2592002141/5000000000 : ℝ)|=(2592002141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-546731849/2500000000 : ℝ)|^2151 ≤ (2720433549821/20000000000000 : ℝ)^1639
        have hw : |(-546731849/2500000000 : ℝ)|=(546731849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320387467/10000000000 : ℝ)*x 0 + (125656713/312500000 : ℝ)*x 1 + (1160114643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320387467/10000000000 : ℝ)^2151 ≤ (4155040386273/12500000000000 : ℝ)^1639 := by
    have hnat : (4320387467 : ℕ)^2151*12500000000000^1639 ≤ 4155040386273^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320387467 10000000000 4155040386273 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125656713/312500000 : ℝ)^2151 ≤ (3781341036643/12500000000000 : ℝ)^1639 := by
    have hnat : (125656713 : ℕ)^2151*12500000000000^1639 ≤ 3781341036643^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125656713 312500000 3781341036643 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1160114643/2500000000 : ℝ)^2151 ≤ (2281809287513/6250000000000 : ℝ)^1639 := by
    have hnat : (1160114643 : ℕ)^2151*6250000000000^1639 ≤ 2281809287513^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160114643 2500000000 2281809287513 6250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320387467/10000000000 : ℝ), (125656713/312500000 : ℝ), (1160114643/2500000000 : ℝ)] ![(4155040386273/12500000000000 : ℝ), (3781341036643/12500000000000 : ℝ), (2281809287513/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320387467/10000000000 : ℝ)|^2151 ≤ (4155040386273/12500000000000 : ℝ)^1639
        have hw : |(4320387467/10000000000 : ℝ)|=(4320387467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125656713/312500000 : ℝ)|^2151 ≤ (3781341036643/12500000000000 : ℝ)^1639
        have hw : |(125656713/312500000 : ℝ)|=(125656713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1160114643/2500000000 : ℝ)|^2151 ≤ (2281809287513/6250000000000 : ℝ)^1639
        have hw : |(1160114643/2500000000 : ℝ)|=(1160114643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2034183767/10000000000 : ℝ)*x 0 + (2592929601/5000000000 : ℝ)*x 1 + (5477869981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034183767/10000000000 : ℝ)^2151 ≤ (12369189307571/100000000000000 : ℝ)^1639 := by
    have hnat : (2034183767 : ℕ)^2151*100000000000000^1639 ≤ 12369189307571^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034183767 10000000000 12369189307571 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592929601/5000000000 : ℝ)^2151 ≤ (42241061275003/100000000000000 : ℝ)^1639 := by
    have hnat : (2592929601 : ℕ)^2151*100000000000000^1639 ≤ 42241061275003^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592929601 5000000000 42241061275003 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477869981/10000000000 : ℝ)^2151 ≤ (45389749398119/100000000000000 : ℝ)^1639 := by
    have hnat : (5477869981 : ℕ)^2151*100000000000000^1639 ≤ 45389749398119^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477869981 10000000000 45389749398119 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2034183767/10000000000 : ℝ), (2592929601/5000000000 : ℝ), (5477869981/10000000000 : ℝ)] ![(12369189307571/100000000000000 : ℝ), (42241061275003/100000000000000 : ℝ), (45389749398119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2034183767/10000000000 : ℝ)|^2151 ≤ (12369189307571/100000000000000 : ℝ)^1639
        have hw : |(-2034183767/10000000000 : ℝ)|=(2034183767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592929601/5000000000 : ℝ)|^2151 ≤ (42241061275003/100000000000000 : ℝ)^1639
        have hw : |(2592929601/5000000000 : ℝ)|=(2592929601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477869981/10000000000 : ℝ)|^2151 ≤ (45389749398119/100000000000000 : ℝ)^1639
        have hw : |(5477869981/10000000000 : ℝ)|=(5477869981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (528972501/1000000000 : ℝ)*x 0 + (-1893061479/10000000000 : ℝ)*x 1 + (5477869981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528972501/1000000000 : ℝ)^2151 ≤ (43354838906909/100000000000000 : ℝ)^1639 := by
    have hnat : (528972501 : ℕ)^2151*100000000000000^1639 ≤ 43354838906909^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528972501 1000000000 43354838906909 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893061479/10000000000 : ℝ)^2151 ≤ (351731614993/3125000000000 : ℝ)^1639 := by
    have hnat : (1893061479 : ℕ)^2151*3125000000000^1639 ≤ 351731614993^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893061479 10000000000 351731614993 3125000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477869981/10000000000 : ℝ)^2151 ≤ (45389749398119/100000000000000 : ℝ)^1639 := by
    have hnat : (5477869981 : ℕ)^2151*100000000000000^1639 ≤ 45389749398119^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477869981 10000000000 45389749398119 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528972501/1000000000 : ℝ), (-1893061479/10000000000 : ℝ), (5477869981/10000000000 : ℝ)] ![(43354838906909/100000000000000 : ℝ), (351731614993/3125000000000 : ℝ), (45389749398119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528972501/1000000000 : ℝ)|^2151 ≤ (43354838906909/100000000000000 : ℝ)^1639
        have hw : |(528972501/1000000000 : ℝ)|=(528972501/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1893061479/10000000000 : ℝ)|^2151 ≤ (351731614993/3125000000000 : ℝ)^1639
        have hw : |(-1893061479/10000000000 : ℝ)|=(1893061479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477869981/10000000000 : ℝ)|^2151 ≤ (45389749398119/100000000000000 : ℝ)^1639
        have hw : |(5477869981/10000000000 : ℝ)|=(5477869981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644862513/5000000000 : ℝ)*x 0 + (1369467497/2500000000 : ℝ)*x 1 + (-1893061447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644862513/5000000000 : ℝ)^2151 ≤ (43354839079011/100000000000000 : ℝ)^1639 := by
    have hnat : (2644862513 : ℕ)^2151*100000000000000^1639 ≤ 43354839079011^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644862513 5000000000 43354839079011 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369467497/2500000000 : ℝ)^2151 ≤ (141842967107/312500000000 : ℝ)^1639 := by
    have hnat : (1369467497 : ℕ)^2151*312500000000^1639 ≤ 141842967107^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369467497 2500000000 141842967107 312500000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893061447/10000000000 : ℝ)^2151 ≤ (5627705715041/50000000000000 : ℝ)^1639 := by
    have hnat : (1893061447 : ℕ)^2151*50000000000000^1639 ≤ 5627705715041^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893061447 10000000000 5627705715041 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644862513/5000000000 : ℝ), (1369467497/2500000000 : ℝ), (-1893061447/10000000000 : ℝ)] ![(43354839079011/100000000000000 : ℝ), (141842967107/312500000000 : ℝ), (5627705715041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644862513/5000000000 : ℝ)|^2151 ≤ (43354839079011/100000000000000 : ℝ)^1639
        have hw : |(2644862513/5000000000 : ℝ)|=(2644862513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369467497/2500000000 : ℝ)|^2151 ≤ (141842967107/312500000000 : ℝ)^1639
        have hw : |(1369467497/2500000000 : ℝ)|=(1369467497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893061447/10000000000 : ℝ)|^2151 ≤ (5627705715041/50000000000000 : ℝ)^1639
        have hw : |(-1893061447/10000000000 : ℝ)|=(1893061447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s2_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320525973/10000000000 : ℝ)*x 0 + (92731467/200000000 : ℝ)*x 1 + (4024935107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320525973/10000000000 : ℝ)^2151 ≤ (132966886519/400000000000 : ℝ)^1639 := by
    have hnat : (4320525973 : ℕ)^2151*400000000000^1639 ≤ 132966886519^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320525973 10000000000 132966886519 400000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92731467/200000000 : ℝ)^2151 ≤ (284912797053/781250000000 : ℝ)^1639 := by
    have hnat : (92731467 : ℕ)^2151*781250000000^1639 ≤ 284912797053^1639*200000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92731467 200000000 284912797053 781250000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024935107/10000000000 : ℝ)^2151 ≤ (15144720165713/50000000000000 : ℝ)^1639 := by
    have hnat : (4024935107 : ℕ)^2151*50000000000000^1639 ≤ 15144720165713^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024935107 10000000000 15144720165713 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320525973/10000000000 : ℝ), (92731467/200000000 : ℝ), (4024935107/10000000000 : ℝ)] ![(132966886519/400000000000 : ℝ), (284912797053/781250000000 : ℝ), (15144720165713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320525973/10000000000 : ℝ)|^2151 ≤ (132966886519/400000000000 : ℝ)^1639
        have hw : |(4320525973/10000000000 : ℝ)|=(4320525973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92731467/200000000 : ℝ)|^2151 ≤ (284912797053/781250000000 : ℝ)^1639
        have hw : |(92731467/200000000 : ℝ)|=(92731467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024935107/10000000000 : ℝ)|^2151 ≤ (15144720165713/50000000000000 : ℝ)^1639
        have hw : |(4024935107/10000000000 : ℝ)|=(4024935107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (689/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2463/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2013/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19461/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (689/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19461/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (689/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19461/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (689/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19461/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (689/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19461/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (689/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19461/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (689/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (689/10000 : ℝ) ^ (4301/1024 : ℝ) ≤ (131914890622479/10000000000000000000 : ℝ) := by
    have hpowers : (689/10000 : ℝ)^4301 ≤ (131914890622479/10000000000000000000 : ℝ)^1024 := by
      have hnat : (689 : ℕ)^4301*10000000000000000000^1024 ≤ 131914890622479^1024*10000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        689 10000 131914890622479 10000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (689/10000 : ℝ)) (X := (131914890622479/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19461/100000 : ℝ) ^ (4301/1024 : ℝ) ≤ (25840137177665143/25000000000000000000 : ℝ) := by
    have hpowers : (19461/100000 : ℝ)^4301 ≤ (25840137177665143/25000000000000000000 : ℝ)^1024 := by
      have hnat : (19461 : ℕ)^4301*25000000000000000000^1024 ≤ 25840137177665143^1024*100000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19461 100000 25840137177665143 25000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19461/100000 : ℝ)) (X := (25840137177665143/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000131914890622479/5000000000000000000 : ℝ) ≤ (10000062813062241/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (5000131914890622479/5000000000000000000 : ℝ)^1024 ≤ (10000062813062241/10000000000000000 : ℝ)^4301 := by
      have hnat : (5000131914890622479 : ℕ)^1024*10000000000000000^4301 ≤ 10000062813062241^4301*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000131914890622479 5000000000000000000 10000062813062241 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062813062241/10000000000000000 : ℝ)) (X := (5000131914890622479/5000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50052339848808442681/50000000000000000000 : ℝ) ≤ (10002491264589427/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (50052339848808442681/50000000000000000000 : ℝ)^1024 ≤ (10002491264589427/10000000000000000 : ℝ)^4301 := by
      have hnat : (50052339848808442681 : ℕ)^1024*10000000000000000^4301 ≤ 10002491264589427^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50052339848808442681 50000000000000000000 10002491264589427 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002491264589427/10000000000000000 : ℝ)) (X := (50052339848808442681/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12525840137177665143/12500000000000000000 : ℝ) ≤ (10004919716116613/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (12525840137177665143/12500000000000000000 : ℝ)^1024 ≤ (10004919716116613/10000000000000000 : ℝ)^4301 := by
      have hnat : (12525840137177665143 : ℕ)^1024*10000000000000000^4301 ≤ 10004919716116613^4301*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12525840137177665143 12500000000000000000 10004919716116613 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004919716116613/10000000000000000 : ℝ)) (X := (12525840137177665143/12500000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(131914890622479/10000000000000000000 : ℝ) ≤ ((9667486581612369887/9670000000000000000 : ℝ)+2*(1214225763593/628550000000000 : ℝ)*(689/10000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (9667486581612369887/9670000000000000000 : ℝ)+2*(1214225763593/628550000000000 : ℝ)*(689/10000 : ℝ)=(10000062813062241/10000000000000000 : ℝ) by norm_num, show 1+2*(131914890622479/10000000000000000000 : ℝ)=(5000131914890622479/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25840137177665143/25000000000000000000 : ℝ)+(131914890622479/10000000000000000000 : ℝ) ≤ ((9667486581612369887/9670000000000000000 : ℝ)+(1214225763593/628550000000000 : ℝ)*((19461/100000 : ℝ)+(689/10000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (9667486581612369887/9670000000000000000 : ℝ)+(1214225763593/628550000000000 : ℝ)*((19461/100000 : ℝ)+(689/10000 : ℝ))=(10002491264589427/10000000000000000 : ℝ) by norm_num, show 1+(25840137177665143/25000000000000000000 : ℝ)+(131914890622479/10000000000000000000 : ℝ)=(50052339848808442681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25840137177665143/25000000000000000000 : ℝ) ≤ ((9667486581612369887/9670000000000000000 : ℝ)+2*(1214225763593/628550000000000 : ℝ)*(19461/100000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (9667486581612369887/9670000000000000000 : ℝ)+2*(1214225763593/628550000000000 : ℝ)*(19461/100000 : ℝ)=(10004919716116613/10000000000000000 : ℝ) by norm_num, show 1+2*(25840137177665143/25000000000000000000 : ℝ)=(12525840137177665143/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9667486581612369887/9670000000000000000 : ℝ)*(X 1 0+X 2 0)+(1214225763593/628550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (689/10000 : ℝ)) (hi := (19461/100000 : ℝ)) (c := (9667486581612369887/9670000000000000000 : ℝ)) (alpha := (1214225763593/628550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9667486581612369887/9670000000000000000 : ℝ)*(X 0 1+X 2 1)+(1214225763593/628550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (689/10000 : ℝ)) (hi := (19461/100000 : ℝ)) (c := (9667486581612369887/9670000000000000000 : ℝ)) (alpha := (1214225763593/628550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9667486581612369887/9670000000000000000 : ℝ)*(X 0 2+X 1 2)+(1214225763593/628550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (689/10000 : ℝ)) (hi := (19461/100000 : ℝ)) (c := (9667486581612369887/9670000000000000000 : ℝ)) (alpha := (1214225763593/628550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2034117811/10000000000 : ℝ)*X 0 0+(1369935479/2500000000 : ℝ)*X 0 1+(5184003989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682975699/5000000000 : ℝ)*X 1 0+(-109346369/500000000 : ℝ)*X 1 1+(259200219/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5365951483/10000000000 : ℝ)*X 2 0+(2592002141/5000000000 : ℝ)*X 2 1+(-546731849/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320387467/10000000000 : ℝ)*X 0 0+(125656713/312500000 : ℝ)*X 0 1+(1160114643/2500000000 : ℝ)*X 0 2+(4320387467/10000000000 : ℝ)*X 1 0+(125656713/312500000 : ℝ)*X 1 1+(1160114643/2500000000 : ℝ)*X 1 2+(4320387467/10000000000 : ℝ)*X 2 0+(125656713/312500000 : ℝ)*X 2 1+(1160114643/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2034183767/10000000000 : ℝ)*X 0 0+(2592929601/5000000000 : ℝ)*X 0 1+(5477869981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528972501/1000000000 : ℝ)*X 1 0+(-1893061479/10000000000 : ℝ)*X 1 1+(5477869981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644862513/5000000000 : ℝ)*X 2 0+(1369467497/2500000000 : ℝ)*X 2 1+(-1893061447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320525973/10000000000 : ℝ)*X 0 0+(92731467/200000000 : ℝ)*X 0 1+(4024935107/10000000000 : ℝ)*X 0 2+(4320525973/10000000000 : ℝ)*X 1 0+(92731467/200000000 : ℝ)*X 1 1+(4024935107/10000000000 : ℝ)*X 1 2+(4320525973/10000000000 : ℝ)*X 2 0+(92731467/200000000 : ℝ)*X 2 1+(4024935107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16391074964925599907215567499/3142750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (854984541/100000000000000 : ℝ)*(base19) + (902267071/100000000000000 : ℝ)*(base23) + (134813/4000000000000 : ℝ)*(lower2) + (113938167/100000000000000 : ℝ)*(upper3) + (107476507/100000000000000 : ℝ)*(upper5) + (2497882415061913/100000000000000 : ℝ)*(major0) + (2497882415061913/100000000000000 : ℝ)*(major1) + (1248941207530957/50000000000000 : ℝ)*(major2) + (3381386500863531/100000000000000 : ℝ)*(sp0) + (169070013979157/5000000000000 : ℝ)*(sp1) + (3381400232300611/100000000000000 : ℝ)*(sp2) + (201794676926063/12500000000000 : ℝ)*(sp3) + (14633704151/100000000000000 : ℝ)*(sp4) + (6106296969/100000000000000 : ℝ)*(sp7) + (3153053753331/195312500000 : ℝ)*(f.failure) + (1690700567283841/50000000000000 : ℝ)*(f.sum) + (221083766053637/31427500000000000000000000000 : ℝ)*base66 + (54722943982151979803/12571000000000000000000000000000000 : ℝ)*base67 + (4225577141257594167/6285500000000000000000000000000000 : ℝ)*base69 + (6407052036128979803/12571000000000000000000000000000000 : ℝ)*base71 + (104313765310559/62855000000000000000000000000 : ℝ)*base74 + (91672363893452594167/6285500000000000000000000000000000 : ℝ)*base75 + (209516771902992620197/12571000000000000000000000000000000 : ℝ)*base78 + (75124439762250620197/12571000000000000000000000000000000 : ℝ)*base80 + (117197009316007/62855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (192523/39062500000000000000 : ℝ)*base90 + (192523/39062500000000000000 : ℝ)*base92 + (145787/9765625000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (486660420188722796037501/62855000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1571907559/100000000000000 : ℝ)*(base19) + (35588017/2000000000000 : ℝ)*(base23) + (39038863/20000000000000 : ℝ)*(upper3) + (2449291/3125000000000 : ℝ)*(lower4) + (61190131/50000000000000 : ℝ)*(upper5) + (2529741373493543/100000000000000 : ℝ)*(major0) + (2529741373493543/100000000000000 : ℝ)*(major1) + (2529741373493543/100000000000000 : ℝ)*(major2) + (3509377887/20000000000000 : ℝ)*(sp1) + (4188973133/20000000000000 : ℝ)*(sp2) + (68490575008991/2000000000000 : ℝ)*(sp4) + (1712254815826277/50000000000000 : ℝ)*(sp5) + (1712253013091517/50000000000000 : ℝ)*(sp6) + (326990747690247/20000000000000 : ℝ)*(sp7) + (326990747690247/20000000000000 : ℝ)*(f.failure) + (68490575008991/2000000000000 : ℝ)*(f.sum) + (27314662843277/62855000000000000000000000000 : ℝ)*base66 + (2875390636462384667/12571000000000000000000000000000000 : ℝ)*base68 + (19097252222457384667/12571000000000000000000000000000000 : ℝ)*base70 + (49081357221812615333/12571000000000000000000000000000000 : ℝ)*base71 + (77387577328839/31427500000000000000000000000 : ℝ)*base73 + (116740596253638615333/12571000000000000000000000000000000 : ℝ)*base75 + (23014388883726384667/12571000000000000000000000000000000 : ℝ)*base78 + (35919947044975615333/12571000000000000000000000000000000 : ℝ)*base79 + (101482347217013/62855000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6540613/2000000000000000000000 : ℝ)*base90 + (6540613/2000000000000000000000 : ℝ)*base92 + (6540613/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1342_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19461/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (689/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1342_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1342_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1342_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1342_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2463/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2013/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1342_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
