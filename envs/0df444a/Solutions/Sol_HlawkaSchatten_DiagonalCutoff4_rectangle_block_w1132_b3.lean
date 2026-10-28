-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:27:39.288693+00:00
-- url     : https://prove2.me/submissions/725fb3e3-aedc-430e-8cd9-b22b0816e19a

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
theorem support_rectangle_w1132_s9_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534478003/1000000000 : ℝ)*x 0 + (210625183/400000000 : ℝ)*x 1 + (-559092013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534478003/1000000000 : ℝ)^8325 ≤ (8713474412607/20000000000000 : ℝ)^6277 := by
    have hnat : (534478003 : ℕ)^8325*20000000000000^6277 ≤ 8713474412607^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534478003 1000000000 8713474412607 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210625183/400000000 : ℝ)^8325 ≤ (8542751005009/20000000000000 : ℝ)^6277 := by
    have hnat : (210625183 : ℕ)^8325*20000000000000^6277 ≤ 8542751005009^6277*400000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210625183 400000000 8542751005009 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559092013/2500000000 : ℝ)^8325 ≤ (6859436450689/50000000000000 : ℝ)^6277 := by
    have hnat : (559092013 : ℕ)^8325*50000000000000^6277 ≤ 6859436450689^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559092013 2500000000 6859436450689 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534478003/1000000000 : ℝ), (210625183/400000000 : ℝ), (-559092013/2500000000 : ℝ)] ![(8713474412607/20000000000000 : ℝ), (8542751005009/20000000000000 : ℝ), (6859436450689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534478003/1000000000 : ℝ)|^8325 ≤ (8713474412607/20000000000000 : ℝ)^6277
        have hw : |(534478003/1000000000 : ℝ)|=(534478003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210625183/400000000 : ℝ)|^8325 ≤ (8542751005009/20000000000000 : ℝ)^6277
        have hw : |(210625183/400000000 : ℝ)|=(210625183/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-559092013/2500000000 : ℝ)|^8325 ≤ (6859436450689/50000000000000 : ℝ)^6277
        have hw : |(-559092013/2500000000 : ℝ)|=(559092013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s9_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171684311/10000000000 : ℝ)*x 0 + (5265948581/10000000000 : ℝ)*x 1 + (539283969/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171684311/10000000000 : ℝ)^8325 ≤ (13195109908367/100000000000000 : ℝ)^6277 := by
    have hnat : (2171684311 : ℕ)^8325*100000000000000^6277 ≤ 13195109908367^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171684311 10000000000 13195109908367 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265948581/10000000000 : ℝ)^8325 ≤ (42717187067927/100000000000000 : ℝ)^6277 := by
    have hnat : (5265948581 : ℕ)^8325*100000000000000^6277 ≤ 42717187067927^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265948581 10000000000 42717187067927 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539283969/1000000000 : ℝ)^8325 ≤ (44087703006193/100000000000000 : ℝ)^6277 := by
    have hnat : (539283969 : ℕ)^8325*100000000000000^6277 ≤ 44087703006193^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539283969 1000000000 44087703006193 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171684311/10000000000 : ℝ), (5265948581/10000000000 : ℝ), (539283969/1000000000 : ℝ)] ![(13195109908367/100000000000000 : ℝ), (42717187067927/100000000000000 : ℝ), (44087703006193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171684311/10000000000 : ℝ)|^8325 ≤ (13195109908367/100000000000000 : ℝ)^6277
        have hw : |(-2171684311/10000000000 : ℝ)|=(2171684311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265948581/10000000000 : ℝ)|^8325 ≤ (42717187067927/100000000000000 : ℝ)^6277
        have hw : |(5265948581/10000000000 : ℝ)|=(5265948581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539283969/1000000000 : ℝ)|^8325 ≤ (44087703006193/100000000000000 : ℝ)^6277
        have hw : |(539283969/1000000000 : ℝ)|=(539283969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s9_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132812357/250000000 : ℝ)*x 0 + (-2109156713/10000000000 : ℝ)*x 1 + (5392839671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132812357/250000000 : ℝ)^8325 ≤ (21609338516233/50000000000000 : ℝ)^6277 := by
    have hnat : (132812357 : ℕ)^8325*50000000000000^6277 ≤ 21609338516233^6277*250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132812357 250000000 21609338516233 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109156713/10000000000 : ℝ)^8325 ≤ (6346810076947/50000000000000 : ℝ)^6277 := by
    have hnat : (2109156713 : ℕ)^8325*50000000000000^6277 ≤ 6346810076947^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109156713 10000000000 6346810076947 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392839671/10000000000 : ℝ)^8325 ≤ (5510962850023/12500000000000 : ℝ)^6277 := by
    have hnat : (5392839671 : ℕ)^8325*12500000000000^6277 ≤ 5510962850023^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392839671 10000000000 5510962850023 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132812357/250000000 : ℝ), (-2109156713/10000000000 : ℝ), (5392839671/10000000000 : ℝ)] ![(21609338516233/50000000000000 : ℝ), (6346810076947/50000000000000 : ℝ), (5510962850023/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132812357/250000000 : ℝ)|^8325 ≤ (21609338516233/50000000000000 : ℝ)^6277
        have hw : |(132812357/250000000 : ℝ)|=(132812357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109156713/10000000000 : ℝ)|^8325 ≤ (6346810076947/50000000000000 : ℝ)^6277
        have hw : |(-2109156713/10000000000 : ℝ)|=(2109156713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392839671/10000000000 : ℝ)|^8325 ≤ (5510962850023/12500000000000 : ℝ)^6277
        have hw : |(5392839671/10000000000 : ℝ)|=(5392839671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s9_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656247163/5000000000 : ℝ)*x 0 + (269641983/500000000 : ℝ)*x 1 + (-1054578333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656247163/5000000000 : ℝ)^8325 ≤ (43218677528787/100000000000000 : ℝ)^6277 := by
    have hnat : (2656247163 : ℕ)^8325*100000000000000^6277 ≤ 43218677528787^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656247163 5000000000 43218677528787 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269641983/500000000 : ℝ)^8325 ≤ (11021925670229/25000000000000 : ℝ)^6277 := by
    have hnat : (269641983 : ℕ)^8325*25000000000000^6277 ≤ 11021925670229^6277*500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269641983 500000000 11021925670229 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054578333/5000000000 : ℝ)^8325 ≤ (6346809889371/50000000000000 : ℝ)^6277 := by
    have hnat : (1054578333 : ℕ)^8325*50000000000000^6277 ≤ 6346809889371^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054578333 5000000000 6346809889371 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656247163/5000000000 : ℝ), (269641983/500000000 : ℝ), (-1054578333/5000000000 : ℝ)] ![(43218677528787/100000000000000 : ℝ), (11021925670229/25000000000000 : ℝ), (6346809889371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656247163/5000000000 : ℝ)|^8325 ≤ (43218677528787/100000000000000 : ℝ)^6277
        have hw : |(2656247163/5000000000 : ℝ)|=(2656247163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269641983/500000000 : ℝ)|^8325 ≤ (11021925670229/25000000000000 : ℝ)^6277
        have hw : |(269641983/500000000 : ℝ)|=(269641983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054578333/5000000000 : ℝ)|^8325 ≤ (6346809889371/50000000000000 : ℝ)^6277
        have hw : |(-1054578333/5000000000 : ℝ)|=(1054578333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s9_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873219241/2000000000 : ℝ)*x 0 + (2246947237/5000000000 : ℝ)*x 1 + (4241942947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873219241/2000000000 : ℝ)^8325 ≤ (1665851800463/5000000000000 : ℝ)^6277 := by
    have hnat : (873219241 : ℕ)^8325*5000000000000^6277 ≤ 1665851800463^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873219241 2000000000 1665851800463 5000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246947237/5000000000 : ℝ)^8325 ≤ (34616563850343/100000000000000 : ℝ)^6277 := by
    have hnat : (2246947237 : ℕ)^8325*100000000000000^6277 ≤ 34616563850343^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246947237 5000000000 34616563850343 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241942947/10000000000 : ℝ)^8325 ≤ (32066400127969/100000000000000 : ℝ)^6277 := by
    have hnat : (4241942947 : ℕ)^8325*100000000000000^6277 ≤ 32066400127969^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241942947 10000000000 32066400127969 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873219241/2000000000 : ℝ), (2246947237/5000000000 : ℝ), (4241942947/10000000000 : ℝ)] ![(1665851800463/5000000000000 : ℝ), (34616563850343/100000000000000 : ℝ), (32066400127969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873219241/2000000000 : ℝ)|^8325 ≤ (1665851800463/5000000000000 : ℝ)^6277
        have hw : |(873219241/2000000000 : ℝ)|=(873219241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246947237/5000000000 : ℝ)|^8325 ≤ (34616563850343/100000000000000 : ℝ)^6277
        have hw : |(2246947237/5000000000 : ℝ)|=(2246947237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241942947/10000000000 : ℝ)|^8325 ≤ (32066400127969/100000000000000 : ℝ)^6277
        have hw : |(4241942947/10000000000 : ℝ)|=(4241942947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11341/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (7188606834047111/50000000000000000000 : ℝ) := by
    have hpowers : (11341/100000 : ℝ)^2081 ≤ (7188606834047111/50000000000000000000 : ℝ)^512 := by
      have hnat : (11341 : ℕ)^2081*50000000000000000000^512 ≤ 7188606834047111^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11341 100000 7188606834047111 50000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11341/100000 : ℝ)) (X := (7188606834047111/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14043/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (8567038491105029/25000000000000000000 : ℝ) := by
    have hpowers : (14043/100000 : ℝ)^2081 ≤ (8567038491105029/25000000000000000000 : ℝ)^512 := by
      have hnat : (14043 : ℕ)^2081*25000000000000000000^512 ≤ 8567038491105029^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14043 100000 8567038491105029 25000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14043/100000 : ℝ)) (X := (8567038491105029/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007188606834047111/25000000000000000000 : ℝ) ≤ (10000707384487469/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (25007188606834047111/25000000000000000000 : ℝ)^512 ≤ (10000707384487469/10000000000000000 : ℝ)^2081 := by
      have hnat : (25007188606834047111 : ℕ)^512*10000000000000000^2081 ≤ 10000707384487469^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007188606834047111 25000000000000000000 10000707384487469 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707384487469/10000000000000000 : ℝ)) (X := (25007188606834047111/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024322683816257169/50000000000000000000 : ℝ) ≤ (10001196629604823/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50024322683816257169/50000000000000000000 : ℝ)^512 ≤ (10001196629604823/10000000000000000 : ℝ)^2081 := by
      have hnat : (50024322683816257169 : ℕ)^512*10000000000000000^2081 ≤ 10001196629604823^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024322683816257169 50000000000000000000 10001196629604823 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001196629604823/10000000000000000 : ℝ)) (X := (50024322683816257169/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508567038491105029/12500000000000000000 : ℝ) ≤ (10001685874722177/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (12508567038491105029/12500000000000000000 : ℝ)^512 ≤ (10001685874722177/10000000000000000 : ℝ)^2081 := by
      have hnat : (12508567038491105029 : ℕ)^512*10000000000000000^2081 ≤ 10001685874722177^2081*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508567038491105029 12500000000000000000 10001685874722177 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001685874722177/10000000000000000 : ℝ)) (X := (12508567038491105029/12500000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7188606834047111/50000000000000000000 : ℝ) ≤ ((385868775644761683/386000000000000000 : ℝ)+2*(34946079811/19300000000000 : ℝ)*(11341/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (385868775644761683/386000000000000000 : ℝ)+2*(34946079811/19300000000000 : ℝ)*(11341/100000 : ℝ)=(10000707384487469/10000000000000000 : ℝ) by norm_num, show 1+2*(7188606834047111/50000000000000000000 : ℝ)=(25007188606834047111/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8567038491105029/25000000000000000000 : ℝ)+(7188606834047111/50000000000000000000 : ℝ) ≤ ((385868775644761683/386000000000000000 : ℝ)+(34946079811/19300000000000 : ℝ)*((14043/100000 : ℝ)+(11341/100000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (385868775644761683/386000000000000000 : ℝ)+(34946079811/19300000000000 : ℝ)*((14043/100000 : ℝ)+(11341/100000 : ℝ))=(10001196629604823/10000000000000000 : ℝ) by norm_num, show 1+(8567038491105029/25000000000000000000 : ℝ)+(7188606834047111/50000000000000000000 : ℝ)=(50024322683816257169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8567038491105029/25000000000000000000 : ℝ) ≤ ((385868775644761683/386000000000000000 : ℝ)+2*(34946079811/19300000000000 : ℝ)*(14043/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (385868775644761683/386000000000000000 : ℝ)+2*(34946079811/19300000000000 : ℝ)*(14043/100000 : ℝ)=(10001685874722177/10000000000000000 : ℝ) by norm_num, show 1+2*(8567038491105029/25000000000000000000 : ℝ)=(12508567038491105029/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (385868775644761683/386000000000000000 : ℝ)*(X 1 0+X 2 0)+(34946079811/19300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (385868775644761683/386000000000000000 : ℝ)) (alpha := (34946079811/19300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (385868775644761683/386000000000000000 : ℝ)*(X 0 1+X 2 1)+(34946079811/19300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (385868775644761683/386000000000000000 : ℝ)) (alpha := (34946079811/19300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (385868775644761683/386000000000000000 : ℝ)*(X 0 2+X 1 2)+(34946079811/19300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (14043/100000 : ℝ)) (c := (385868775644761683/386000000000000000 : ℝ)) (alpha := (34946079811/19300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((534478003/1000000000 : ℝ)*X 2 0+(210625183/400000000 : ℝ)*X 2 1+(-559092013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2171684311/10000000000 : ℝ)*X 0 0+(5265948581/10000000000 : ℝ)*X 0 1+(539283969/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132812357/250000000 : ℝ)*X 1 0+(-2109156713/10000000000 : ℝ)*X 1 1+(5392839671/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656247163/5000000000 : ℝ)*X 2 0+(269641983/500000000 : ℝ)*X 2 1+(-1054578333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((873219241/2000000000 : ℝ)*X 0 0+(2246947237/5000000000 : ℝ)*X 0 1+(4241942947/10000000000 : ℝ)*X 0 2+(873219241/2000000000 : ℝ)*X 1 0+(2246947237/5000000000 : ℝ)*X 1 1+(4241942947/10000000000 : ℝ)*X 1 2+(873219241/2000000000 : ℝ)*X 2 0+(2246947237/5000000000 : ℝ)*X 2 1+(4241942947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12111103531162614806209659/4825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169372417/50000000000000 : ℝ)*(base19) + (566260879/100000000000000 : ℝ)*(base23) + (12902819/12500000000000 : ℝ)*(lower1) + (37869161/100000000000000 : ℝ)*(upper3) + (62720331/100000000000000 : ℝ)*(lower4) + (39635109/100000000000000 : ℝ)*(upper5) + (1481222163939891/25000000000000 : ℝ)*(major0) + (1481222163939891/25000000000000 : ℝ)*(major1) + (1481222163939891/25000000000000 : ℝ)*(major2) + (3390961479/50000000000000 : ℝ)*(sp0) + (1970191005755023/25000000000000 : ℝ)*(sp1) + (7880763684275257/100000000000000 : ℝ)*(sp2) + (1576151334967251/20000000000000 : ℝ)*(sp3) + (39690132048299/1000000000000 : ℝ)*(sp4) + (39690132048299/1000000000000 : ℝ)*(f.failure) + (1970191005755023/25000000000000 : ℝ)*(f.sum) + (1190485006371/241250000000000000000000000 : ℝ)*base65 + (159626109957783447/9650000000000000000000000000000 : ℝ)*base68 + (68275395582983447/9650000000000000000000000000000 : ℝ)*base70 + (924988814944983447/9650000000000000000000000000000 : ℝ)*base72 + (4359500014031/965000000000000000000000000 : ℝ)*base74 + (1120398191114533447/9650000000000000000000000000000 : ℝ)*base76 + (3095226723516553/9650000000000000000000000000000 : ℝ)*base77 + (50895716406516553/9650000000000000000000000000000 : ℝ)*base79 + (1056890141853/482500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (695267/100000000000000000000 : ℝ)*base89 + (695267/100000000000000000000 : ℝ)*base91 + (695267/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1132_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_box_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044463387/10000000000 : ℝ)*x 0 + (1344112369/2500000000 : ℝ)*x 1 + (2688224653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044463387/10000000000 : ℝ)^8325 ≤ (12179843423797/100000000000000 : ℝ)^6277 := by
    have hnat : (2044463387 : ℕ)^8325*100000000000000^6277 ≤ 12179843423797^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044463387 10000000000 12179843423797 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344112369/2500000000 : ℝ)^8325 ≤ (43910079200223/100000000000000 : ℝ)^6277 := by
    have hnat : (1344112369 : ℕ)^8325*100000000000000^6277 ≤ 43910079200223^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344112369 2500000000 43910079200223 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688224653/5000000000 : ℝ)^8325 ≤ (43910077358817/100000000000000 : ℝ)^6277 := by
    have hnat : (2688224653 : ℕ)^8325*100000000000000^6277 ≤ 43910077358817^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688224653 5000000000 43910077358817 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044463387/10000000000 : ℝ), (1344112369/2500000000 : ℝ), (2688224653/5000000000 : ℝ)] ![(12179843423797/100000000000000 : ℝ), (43910079200223/100000000000000 : ℝ), (43910077358817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044463387/10000000000 : ℝ)|^8325 ≤ (12179843423797/100000000000000 : ℝ)^6277
        have hw : |(-2044463387/10000000000 : ℝ)|=(2044463387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344112369/2500000000 : ℝ)|^8325 ≤ (43910079200223/100000000000000 : ℝ)^6277
        have hw : |(1344112369/2500000000 : ℝ)|=(1344112369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688224653/5000000000 : ℝ)|^8325 ≤ (43910077358817/100000000000000 : ℝ)^6277
        have hw : |(2688224653/5000000000 : ℝ)|=(2688224653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295890937/10000000000 : ℝ)*x 0 + (-2153689163/10000000000 : ℝ)*x 1 + (3360281/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295890937/10000000000 : ℝ)^8325 ≤ (672494142217/1562500000000 : ℝ)^6277 := by
    have hnat : (5295890937 : ℕ)^8325*1562500000000^6277 ≤ 672494142217^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295890937 10000000000 672494142217 1562500000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153689163/10000000000 : ℝ)^8325 ≤ (6525147164139/50000000000000 : ℝ)^6277 := by
    have hnat : (2153689163 : ℕ)^8325*50000000000000^6277 ≤ 6525147164139^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153689163 10000000000 6525147164139 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3360281/6250000 : ℝ)^8325 ≤ (43910080543367/100000000000000 : ℝ)^6277 := by
    have hnat : (3360281 : ℕ)^8325*100000000000000^6277 ≤ 43910080543367^6277*6250000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3360281 6250000 43910080543367 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295890937/10000000000 : ℝ), (-2153689163/10000000000 : ℝ), (3360281/6250000 : ℝ)] ![(672494142217/1562500000000 : ℝ), (6525147164139/50000000000000 : ℝ), (43910080543367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295890937/10000000000 : ℝ)|^8325 ≤ (672494142217/1562500000000 : ℝ)^6277
        have hw : |(5295890937/10000000000 : ℝ)|=(5295890937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153689163/10000000000 : ℝ)|^8325 ≤ (6525147164139/50000000000000 : ℝ)^6277
        have hw : |(-2153689163/10000000000 : ℝ)|=(2153689163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3360281/6250000 : ℝ)|^8325 ≤ (43910080543367/100000000000000 : ℝ)^6277
        have hw : |(3360281/6250000 : ℝ)|=(3360281/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295891617/10000000000 : ℝ)*x 0 + (5376449267/10000000000 : ℝ)*x 1 + (-2153688701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295891617/10000000000 : ℝ)^8325 ≤ (43039632431323/100000000000000 : ℝ)^6277 := by
    have hnat : (5295891617 : ℕ)^8325*100000000000000^6277 ≤ 43039632431323^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295891617 10000000000 43039632431323 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376449267/10000000000 : ℝ)^8325 ≤ (43910076936377/100000000000000 : ℝ)^6277 := by
    have hnat : (5376449267 : ℕ)^8325*100000000000000^6277 ≤ 43910076936377^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376449267 10000000000 43910076936377 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153688701/10000000000 : ℝ)^8325 ≤ (6525145307697/50000000000000 : ℝ)^6277 := by
    have hnat : (2153688701 : ℕ)^8325*50000000000000^6277 ≤ 6525145307697^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153688701 10000000000 6525145307697 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295891617/10000000000 : ℝ), (5376449267/10000000000 : ℝ), (-2153688701/10000000000 : ℝ)] ![(43039632431323/100000000000000 : ℝ), (43910076936377/100000000000000 : ℝ), (6525145307697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295891617/10000000000 : ℝ)|^8325 ≤ (43039632431323/100000000000000 : ℝ)^6277
        have hw : |(5295891617/10000000000 : ℝ)|=(5295891617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376449267/10000000000 : ℝ)|^8325 ≤ (43910076936377/100000000000000 : ℝ)^6277
        have hw : |(5376449267/10000000000 : ℝ)|=(5376449267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153688701/10000000000 : ℝ)|^8325 ≤ (6525145307697/50000000000000 : ℝ)^6277
        have hw : |(-2153688701/10000000000 : ℝ)|=(2153688701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4473733733/10000000000 : ℝ)*x 0 + (862875499/2000000000 : ℝ)*x 1 + (4314377393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4473733733/10000000000 : ℝ)^8325 ≤ (34410746772733/100000000000000 : ℝ)^6277 := by
    have hnat : (4473733733 : ℕ)^8325*100000000000000^6277 ≤ 34410746772733^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473733733 10000000000 34410746772733 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862875499/2000000000 : ℝ)^8325 ≤ (16397313562537/50000000000000 : ℝ)^6277 := by
    have hnat : (862875499 : ℕ)^8325*50000000000000^6277 ≤ 16397313562537^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862875499 2000000000 16397313562537 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314377393/10000000000 : ℝ)^8325 ≤ (32794626096781/100000000000000 : ℝ)^6277 := by
    have hnat : (4314377393 : ℕ)^8325*100000000000000^6277 ≤ 32794626096781^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314377393 10000000000 32794626096781 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4473733733/10000000000 : ℝ), (862875499/2000000000 : ℝ), (4314377393/10000000000 : ℝ)] ![(34410746772733/100000000000000 : ℝ), (16397313562537/50000000000000 : ℝ), (32794626096781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4473733733/10000000000 : ℝ)|^8325 ≤ (34410746772733/100000000000000 : ℝ)^6277
        have hw : |(4473733733/10000000000 : ℝ)|=(4473733733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862875499/2000000000 : ℝ)|^8325 ≤ (16397313562537/50000000000000 : ℝ)^6277
        have hw : |(862875499/2000000000 : ℝ)|=(862875499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4314377393/10000000000 : ℝ)|^8325 ≤ (32794626096781/100000000000000 : ℝ)^6277
        have hw : |(4314377393/10000000000 : ℝ)|=(4314377393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-287535771/1250000000 : ℝ)*x 0 + (2640507109/5000000000 : ℝ)*x 1 + (5281013003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287535771/1250000000 : ℝ)^8325 ≤ (14241315624323/100000000000000 : ℝ)^6277 := by
    have hnat : (287535771 : ℕ)^8325*100000000000000^6277 ≤ 14241315624323^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287535771 1250000000 14241315624323 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640507109/5000000000 : ℝ)^8325 ≤ (5359918590119/12500000000000 : ℝ)^6277 := by
    have hnat : (2640507109 : ℕ)^8325*12500000000000^6277 ≤ 5359918590119^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640507109 5000000000 5359918590119 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281013003/10000000000 : ℝ)^8325 ≤ (5234293901/12207031250 : ℝ)^6277 := by
    have hnat : (5281013003 : ℕ)^8325*12207031250^6277 ≤ 5234293901^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281013003 10000000000 5234293901 12207031250 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287535771/1250000000 : ℝ), (2640507109/5000000000 : ℝ), (5281013003/10000000000 : ℝ)] ![(14241315624323/100000000000000 : ℝ), (5359918590119/12500000000000 : ℝ), (5234293901/12207031250 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287535771/1250000000 : ℝ)|^8325 ≤ (14241315624323/100000000000000 : ℝ)^6277
        have hw : |(-287535771/1250000000 : ℝ)|=(287535771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640507109/5000000000 : ℝ)|^8325 ≤ (5359918590119/12500000000000 : ℝ)^6277
        have hw : |(2640507109/5000000000 : ℝ)|=(2640507109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281013003/10000000000 : ℝ)|^8325 ≤ (5234293901/12207031250 : ℝ)^6277
        have hw : |(5281013003/10000000000 : ℝ)|=(5281013003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340832983/2500000000 : ℝ)*x 0 + (-2191200413/10000000000 : ℝ)*x 1 + (2640506817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340832983/2500000000 : ℝ)^8325 ≤ (10942012282031/25000000000000 : ℝ)^6277 := by
    have hnat : (1340832983 : ℕ)^8325*25000000000000^6277 ≤ 10942012282031^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340832983 2500000000 10942012282031 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191200413/10000000000 : ℝ)^8325 ≤ (13352608421123/100000000000000 : ℝ)^6277 := by
    have hnat : (2191200413 : ℕ)^8325*100000000000000^6277 ≤ 13352608421123^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191200413 10000000000 13352608421123 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640506817/5000000000 : ℝ)^8325 ≤ (10719835608009/25000000000000 : ℝ)^6277 := by
    have hnat : (2640506817 : ℕ)^8325*25000000000000^6277 ≤ 10719835608009^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640506817 5000000000 10719835608009 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340832983/2500000000 : ℝ), (-2191200413/10000000000 : ℝ), (2640506817/5000000000 : ℝ)] ![(10942012282031/25000000000000 : ℝ), (13352608421123/100000000000000 : ℝ), (10719835608009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340832983/2500000000 : ℝ)|^8325 ≤ (10942012282031/25000000000000 : ℝ)^6277
        have hw : |(1340832983/2500000000 : ℝ)|=(1340832983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191200413/10000000000 : ℝ)|^8325 ≤ (13352608421123/100000000000000 : ℝ)^6277
        have hw : |(-2191200413/10000000000 : ℝ)|=(2191200413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640506817/5000000000 : ℝ)|^8325 ≤ (10719835608009/25000000000000 : ℝ)^6277
        have hw : |(2640506817/5000000000 : ℝ)|=(2640506817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363331713/10000000000 : ℝ)*x 0 + (2640506933/5000000000 : ℝ)*x 1 + (-1095600199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363331713/10000000000 : ℝ)^8325 ≤ (43768046757849/100000000000000 : ℝ)^6277 := by
    have hnat : (5363331713 : ℕ)^8325*100000000000000^6277 ≤ 43768046757849^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363331713 10000000000 43768046757849 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640506933/5000000000 : ℝ)^8325 ≤ (10719836232593/25000000000000 : ℝ)^6277 := by
    have hnat : (2640506933 : ℕ)^8325*25000000000000^6277 ≤ 10719836232593^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640506933 5000000000 10719836232593 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095600199/5000000000 : ℝ)^8325 ≤ (6676304149947/50000000000000 : ℝ)^6277 := by
    have hnat : (1095600199 : ℕ)^8325*50000000000000^6277 ≤ 6676304149947^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095600199 5000000000 6676304149947 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363331713/10000000000 : ℝ), (2640506933/5000000000 : ℝ), (-1095600199/5000000000 : ℝ)] ![(43768046757849/100000000000000 : ℝ), (10719836232593/25000000000000 : ℝ), (6676304149947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363331713/10000000000 : ℝ)|^8325 ≤ (43768046757849/100000000000000 : ℝ)^6277
        have hw : |(5363331713/10000000000 : ℝ)|=(5363331713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640506933/5000000000 : ℝ)|^8325 ≤ (10719836232593/25000000000000 : ℝ)^6277
        have hw : |(2640506933/5000000000 : ℝ)|=(2640506933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095600199/5000000000 : ℝ)|^8325 ≤ (6676304149947/50000000000000 : ℝ)^6277
        have hw : |(-1095600199/5000000000 : ℝ)|=(1095600199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (425808149/1000000000 : ℝ)*x 0 + (4422182839/10000000000 : ℝ)*x 1 + (884436491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425808149/1000000000 : ℝ)^8325 ≤ (32228301695431/100000000000000 : ℝ)^6277 := by
    have hnat : (425808149 : ℕ)^8325*100000000000000^6277 ≤ 32228301695431^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425808149 1000000000 32228301695431 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4422182839/10000000000 : ℝ)^8325 ≤ (16942925549061/50000000000000 : ℝ)^6277 := by
    have hnat : (4422182839 : ℕ)^8325*50000000000000^6277 ≤ 16942925549061^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422182839 10000000000 16942925549061 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884436491/2000000000 : ℝ)^8325 ≤ (16942923597801/50000000000000 : ℝ)^6277 := by
    have hnat : (884436491 : ℕ)^8325*50000000000000^6277 ≤ 16942923597801^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884436491 2000000000 16942923597801 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425808149/1000000000 : ℝ), (4422182839/10000000000 : ℝ), (884436491/2000000000 : ℝ)] ![(32228301695431/100000000000000 : ℝ), (16942925549061/50000000000000 : ℝ), (16942923597801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425808149/1000000000 : ℝ)|^8325 ≤ (32228301695431/100000000000000 : ℝ)^6277
        have hw : |(425808149/1000000000 : ℝ)|=(425808149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4422182839/10000000000 : ℝ)|^8325 ≤ (16942925549061/50000000000000 : ℝ)^6277
        have hw : |(4422182839/10000000000 : ℝ)|=(4422182839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884436491/2000000000 : ℝ)|^8325 ≤ (16942923597801/50000000000000 : ℝ)^6277
        have hw : |(884436491/2000000000 : ℝ)|=(884436491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_8 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-56170033/250000000 : ℝ)*x 0 + (208645083/400000000 : ℝ)*x 1 + (2693028423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56170033/250000000 : ℝ)^8325 ≤ (138038217873/1000000000000 : ℝ)^6277 := by
    have hnat : (56170033 : ℕ)^8325*1000000000000^6277 ≤ 138038217873^6277*250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56170033 250000000 138038217873 1000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208645083/400000000 : ℝ)^8325 ≤ (2636375220917/6250000000000 : ℝ)^6277 := by
    have hnat : (208645083 : ℕ)^8325*6250000000000^6277 ≤ 2636375220917^6277*400000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208645083 400000000 2636375220917 6250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693028423/5000000000 : ℝ)^8325 ≤ (1760566986657/4000000000000 : ℝ)^6277 := by
    have hnat : (2693028423 : ℕ)^8325*4000000000000^6277 ≤ 1760566986657^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693028423 5000000000 1760566986657 4000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56170033/250000000 : ℝ), (208645083/400000000 : ℝ), (2693028423/5000000000 : ℝ)] ![(138038217873/1000000000000 : ℝ), (2636375220917/6250000000000 : ℝ), (1760566986657/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56170033/250000000 : ℝ)|^8325 ≤ (138038217873/1000000000000 : ℝ)^6277
        have hw : |(-56170033/250000000 : ℝ)|=(56170033/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208645083/400000000 : ℝ)|^8325 ≤ (2636375220917/6250000000000 : ℝ)^6277
        have hw : |(208645083/400000000 : ℝ)|=(208645083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693028423/5000000000 : ℝ)|^8325 ≤ (1760566986657/4000000000000 : ℝ)^6277
        have hw : |(2693028423/5000000000 : ℝ)|=(2693028423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_9 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528909871/1000000000 : ℝ)*x 0 + (-85993731/400000000 : ℝ)*x 1 + (215442273/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528909871/1000000000 : ℝ)^8325 ≤ (10741607465019/25000000000000 : ℝ)^6277 := by
    have hnat : (528909871 : ℕ)^8325*25000000000000^6277 ≤ 10741607465019^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528909871 1000000000 10741607465019 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85993731/400000000 : ℝ)^8325 ≤ (13019395682573/100000000000000 : ℝ)^6277 := by
    have hnat : (85993731 : ℕ)^8325*100000000000000^6277 ≤ 13019395682573^6277*400000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85993731 400000000 13019395682573 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215442273/400000000 : ℝ)^8325 ≤ (1760566977553/4000000000000 : ℝ)^6277 := by
    have hnat : (215442273 : ℕ)^8325*4000000000000^6277 ≤ 1760566977553^6277*400000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215442273 400000000 1760566977553 4000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528909871/1000000000 : ℝ), (-85993731/400000000 : ℝ), (215442273/400000000 : ℝ)] ![(10741607465019/25000000000000 : ℝ), (13019395682573/100000000000000 : ℝ), (1760566977553/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528909871/1000000000 : ℝ)|^8325 ≤ (10741607465019/25000000000000 : ℝ)^6277
        have hw : |(528909871/1000000000 : ℝ)|=(528909871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85993731/400000000 : ℝ)|^8325 ≤ (13019395682573/100000000000000 : ℝ)^6277
        have hw : |(-85993731/400000000 : ℝ)|=(85993731/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215442273/400000000 : ℝ)|^8325 ≤ (1760566977553/4000000000000 : ℝ)^6277
        have hw : |(215442273/400000000 : ℝ)|=(215442273/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_10 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644549337/5000000000 : ℝ)*x 0 + (2693028463/5000000000 : ℝ)*x 1 + (-537460797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644549337/5000000000 : ℝ)^8325 ≤ (4296642947221/10000000000000 : ℝ)^6277 := by
    have hnat : (2644549337 : ℕ)^8325*10000000000000^6277 ≤ 4296642947221^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644549337 5000000000 4296642947221 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693028463/5000000000 : ℝ)^8325 ≤ (22007087766737/50000000000000 : ℝ)^6277 := by
    have hnat : (2693028463 : ℕ)^8325*50000000000000^6277 ≤ 22007087766737^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693028463 5000000000 22007087766737 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537460797/2500000000 : ℝ)^8325 ≤ (13019394983801/100000000000000 : ℝ)^6277 := by
    have hnat : (537460797 : ℕ)^8325*100000000000000^6277 ≤ 13019394983801^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537460797 2500000000 13019394983801 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644549337/5000000000 : ℝ), (2693028463/5000000000 : ℝ), (-537460797/2500000000 : ℝ)] ![(4296642947221/10000000000000 : ℝ), (22007087766737/50000000000000 : ℝ), (13019394983801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644549337/5000000000 : ℝ)|^8325 ≤ (4296642947221/10000000000000 : ℝ)^6277
        have hw : |(2644549337/5000000000 : ℝ)|=(2644549337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693028463/5000000000 : ℝ)|^8325 ≤ (22007087766737/50000000000000 : ℝ)^6277
        have hw : |(2693028463/5000000000 : ℝ)|=(2693028463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537460797/2500000000 : ℝ)|^8325 ≤ (13019394983801/100000000000000 : ℝ)^6277
        have hw : |(-537460797/2500000000 : ℝ)|=(537460797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_11 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4495170077/10000000000 : ℝ)*x 0 + (4303518719/10000000000 : ℝ)*x 1 + (4303518781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4495170077/10000000000 : ℝ)^8325 ≤ (34629596383559/100000000000000 : ℝ)^6277 := by
    have hnat : (4495170077 : ℕ)^8325*100000000000000^6277 ≤ 34629596383559^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495170077 10000000000 34629596383559 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303518719/10000000000 : ℝ)^8325 ≤ (1021412546467/3125000000000 : ℝ)^6277 := by
    have hnat : (4303518719 : ℕ)^8325*3125000000000^6277 ≤ 1021412546467^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303518719 10000000000 1021412546467 3125000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4303518781/10000000000 : ℝ)^8325 ≤ (32685202111471/100000000000000 : ℝ)^6277 := by
    have hnat : (4303518781 : ℕ)^8325*100000000000000^6277 ≤ 32685202111471^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303518781 10000000000 32685202111471 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4495170077/10000000000 : ℝ), (4303518719/10000000000 : ℝ), (4303518781/10000000000 : ℝ)] ![(34629596383559/100000000000000 : ℝ), (1021412546467/3125000000000 : ℝ), (32685202111471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4495170077/10000000000 : ℝ)|^8325 ≤ (34629596383559/100000000000000 : ℝ)^6277
        have hw : |(4495170077/10000000000 : ℝ)|=(4495170077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303518719/10000000000 : ℝ)|^8325 ≤ (1021412546467/3125000000000 : ℝ)^6277
        have hw : |(4303518719/10000000000 : ℝ)|=(4303518719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4303518781/10000000000 : ℝ)|^8325 ≤ (32685202111471/100000000000000 : ℝ)^6277
        have hw : |(4303518781/10000000000 : ℝ)|=(4303518781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_12 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098273911/10000000000 : ℝ)*x 0 + (5440050789/10000000000 : ℝ)*x 1 + (2636489921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098273911/10000000000 : ℝ)^8325 ≤ (6303413712179/50000000000000 : ℝ)^6277 := by
    have hnat : (2098273911 : ℕ)^8325*50000000000000^6277 ≤ 6303413712179^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098273911 10000000000 6303413712179 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440050789/10000000000 : ℝ)^8325 ≤ (8920064417643/20000000000000 : ℝ)^6277 := by
    have hnat : (5440050789 : ℕ)^8325*20000000000000^6277 ≤ 8920064417643^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440050789 10000000000 8920064417643 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636489921/5000000000 : ℝ)^8325 ≤ (42792850480689/100000000000000 : ℝ)^6277 := by
    have hnat : (2636489921 : ℕ)^8325*100000000000000^6277 ≤ 42792850480689^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636489921 5000000000 42792850480689 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098273911/10000000000 : ℝ), (5440050789/10000000000 : ℝ), (2636489921/5000000000 : ℝ)] ![(6303413712179/50000000000000 : ℝ), (8920064417643/20000000000000 : ℝ), (42792850480689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098273911/10000000000 : ℝ)|^8325 ≤ (6303413712179/50000000000000 : ℝ)^6277
        have hw : |(-2098273911/10000000000 : ℝ)|=(2098273911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440050789/10000000000 : ℝ)|^8325 ≤ (8920064417643/20000000000000 : ℝ)^6277
        have hw : |(5440050789/10000000000 : ℝ)|=(5440050789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636489921/5000000000 : ℝ)|^8325 ≤ (42792850480689/100000000000000 : ℝ)^6277
        have hw : |(2636489921/5000000000 : ℝ)|=(2636489921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_13 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369007053/10000000000 : ℝ)*x 0 + (-34285951/156250000 : ℝ)*x 1 + (5272979383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369007053/10000000000 : ℝ)^8325 ≤ (5478685318559/12500000000000 : ℝ)^6277 := by
    have hnat : (5369007053 : ℕ)^8325*12500000000000^6277 ≤ 5478685318559^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369007053 10000000000 5478685318559 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34285951/156250000 : ℝ)^8325 ≤ (13377671891339/100000000000000 : ℝ)^6277 := by
    have hnat : (34285951 : ℕ)^8325*100000000000000^6277 ≤ 13377671891339^6277*156250000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34285951 156250000 13377671891339 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272979383/10000000000 : ℝ)^8325 ≤ (21396422770157/50000000000000 : ℝ)^6277 := by
    have hnat : (5272979383 : ℕ)^8325*50000000000000^6277 ≤ 21396422770157^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272979383 10000000000 21396422770157 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369007053/10000000000 : ℝ), (-34285951/156250000 : ℝ), (5272979383/10000000000 : ℝ)] ![(5478685318559/12500000000000 : ℝ), (13377671891339/100000000000000 : ℝ), (21396422770157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369007053/10000000000 : ℝ)|^8325 ≤ (5478685318559/12500000000000 : ℝ)^6277
        have hw : |(5369007053/10000000000 : ℝ)|=(5369007053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34285951/156250000 : ℝ)|^8325 ≤ (13377671891339/100000000000000 : ℝ)^6277
        have hw : |(-34285951/156250000 : ℝ)|=(34285951/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272979383/10000000000 : ℝ)|^8325 ≤ (21396422770157/50000000000000 : ℝ)^6277
        have hw : |(5272979383/10000000000 : ℝ)|=(5272979383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_14 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684503357/5000000000 : ℝ)*x 0 + (5272980019/10000000000 : ℝ)*x 1 + (-274287559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684503357/5000000000 : ℝ)^8325 ≤ (876589577563/2000000000000 : ℝ)^6277 := by
    have hnat : (2684503357 : ℕ)^8325*2000000000000^6277 ≤ 876589577563^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684503357 5000000000 876589577563 2000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272980019/10000000000 : ℝ)^8325 ≤ (42792852385801/100000000000000 : ℝ)^6277 := by
    have hnat : (5272980019 : ℕ)^8325*100000000000000^6277 ≤ 42792852385801^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272980019 10000000000 42792852385801 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274287559/1250000000 : ℝ)^8325 ≤ (13377668721753/100000000000000 : ℝ)^6277 := by
    have hnat : (274287559 : ℕ)^8325*100000000000000^6277 ≤ 13377668721753^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274287559 1250000000 13377668721753 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684503357/5000000000 : ℝ), (5272980019/10000000000 : ℝ), (-274287559/1250000000 : ℝ)] ![(876589577563/2000000000000 : ℝ), (42792852385801/100000000000000 : ℝ), (13377668721753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684503357/5000000000 : ℝ)|^8325 ≤ (876589577563/2000000000000 : ℝ)^6277
        have hw : |(2684503357/5000000000 : ℝ)|=(2684503357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272980019/10000000000 : ℝ)|^8325 ≤ (42792852385801/100000000000000 : ℝ)^6277
        have hw : |(5272980019/10000000000 : ℝ)|=(5272980019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274287559/1250000000 : ℝ)|^8325 ≤ (13377668721753/100000000000000 : ℝ)^6277
        have hw : |(-274287559/1250000000 : ℝ)|=(274287559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_box_15 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059924447/2500000000 : ℝ)*x 0 + (4431252479/10000000000 : ℝ)*x 1 + (4431252227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059924447/2500000000 : ℝ)^8325 ≤ (16021946318203/50000000000000 : ℝ)^6277 := by
    have hnat : (1059924447 : ℕ)^8325*50000000000000^6277 ≤ 16021946318203^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059924447 2500000000 16021946318203 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431252479/10000000000 : ℝ)^8325 ≤ (6795610990717/20000000000000 : ℝ)^6277 := by
    have hnat : (4431252479 : ℕ)^8325*20000000000000^6277 ≤ 6795610990717^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431252479 10000000000 6795610990717 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4431252227/10000000000 : ℝ)^8325 ≤ (8494513097711/25000000000000 : ℝ)^6277 := by
    have hnat : (4431252227 : ℕ)^8325*25000000000000^6277 ≤ 8494513097711^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431252227 10000000000 8494513097711 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059924447/2500000000 : ℝ), (4431252479/10000000000 : ℝ), (4431252227/10000000000 : ℝ)] ![(16021946318203/50000000000000 : ℝ), (6795610990717/20000000000000 : ℝ), (8494513097711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059924447/2500000000 : ℝ)|^8325 ≤ (16021946318203/50000000000000 : ℝ)^6277
        have hw : |(1059924447/2500000000 : ℝ)|=(1059924447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431252479/10000000000 : ℝ)|^8325 ≤ (6795610990717/20000000000000 : ℝ)^6277
        have hw : |(4431252479/10000000000 : ℝ)|=(4431252479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4431252227/10000000000 : ℝ)|^8325 ≤ (8494513097711/25000000000000 : ℝ)^6277
        have hw : |(4431252227/10000000000 : ℝ)|=(4431252227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6223/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59291/100000 : ℝ) ∧ (39889/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41551/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11341/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (7188606834047111/50000000000000000000 : ℝ) := by
    have hpowers : (11341/100000 : ℝ)^2081 ≤ (7188606834047111/50000000000000000000 : ℝ)^512 := by
      have hnat : (11341 : ℕ)^2081*50000000000000000000^512 ≤ 7188606834047111^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11341 100000 7188606834047111 50000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11341/100000 : ℝ)) (X := (7188606834047111/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7021/50000 : ℝ) ^ (2081/512 : ℝ) ≤ (17129118422454971/50000000000000000000 : ℝ) := by
    have hpowers : (7021/50000 : ℝ)^2081 ≤ (17129118422454971/50000000000000000000 : ℝ)^512 := by
      have hnat : (7021 : ℕ)^2081*50000000000000000000^512 ≤ 17129118422454971^512*50000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7021 50000 17129118422454971 50000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7021/50000 : ℝ)) (X := (17129118422454971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007188606834047111/25000000000000000000 : ℝ) ≤ (10000707384487469/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (25007188606834047111/25000000000000000000 : ℝ)^512 ≤ (10000707384487469/10000000000000000 : ℝ)^2081 := by
      have hnat : (25007188606834047111 : ℕ)^512*10000000000000000^2081 ≤ 10000707384487469^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007188606834047111 25000000000000000000 10000707384487469 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000707384487469/10000000000000000 : ℝ)) (X := (25007188606834047111/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012158862628251041/25000000000000000000 : ℝ) ≤ (10001196385697861/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (25012158862628251041/25000000000000000000 : ℝ)^512 ≤ (10001196385697861/10000000000000000 : ℝ)^2081 := by
      have hnat : (25012158862628251041 : ℕ)^512*10000000000000000^2081 ≤ 10001196385697861^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012158862628251041 25000000000000000000 10001196385697861 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001196385697861/10000000000000000 : ℝ)) (X := (25012158862628251041/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017129118422454971/25000000000000000000 : ℝ) ≤ (10001685386908253/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (25017129118422454971/25000000000000000000 : ℝ)^512 ≤ (10001685386908253/10000000000000000 : ℝ)^2081 := by
      have hnat : (25017129118422454971 : ℕ)^512*10000000000000000^2081 ≤ 10001685386908253^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017129118422454971 25000000000000000000 10001685386908253 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001685386908253/10000000000000000 : ℝ)) (X := (25017129118422454971/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7188606834047111/50000000000000000000 : ℝ) ≤ ((1080032764801861697/1080400000000000000 : ℝ)+2*(61125151299/33762500000000 : ℝ)*(11341/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1080032764801861697/1080400000000000000 : ℝ)+2*(61125151299/33762500000000 : ℝ)*(11341/100000 : ℝ)=(10000707384487469/10000000000000000 : ℝ) by norm_num, show 1+2*(7188606834047111/50000000000000000000 : ℝ)=(25007188606834047111/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17129118422454971/50000000000000000000 : ℝ)+(7188606834047111/50000000000000000000 : ℝ) ≤ ((1080032764801861697/1080400000000000000 : ℝ)+(61125151299/33762500000000 : ℝ)*((7021/50000 : ℝ)+(11341/100000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (1080032764801861697/1080400000000000000 : ℝ)+(61125151299/33762500000000 : ℝ)*((7021/50000 : ℝ)+(11341/100000 : ℝ))=(10001196385697861/10000000000000000 : ℝ) by norm_num, show 1+(17129118422454971/50000000000000000000 : ℝ)+(7188606834047111/50000000000000000000 : ℝ)=(25012158862628251041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17129118422454971/50000000000000000000 : ℝ) ≤ ((1080032764801861697/1080400000000000000 : ℝ)+2*(61125151299/33762500000000 : ℝ)*(7021/50000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1080032764801861697/1080400000000000000 : ℝ)+2*(61125151299/33762500000000 : ℝ)*(7021/50000 : ℝ)=(10001685386908253/10000000000000000 : ℝ) by norm_num, show 1+2*(17129118422454971/50000000000000000000 : ℝ)=(25017129118422454971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1080032764801861697/1080400000000000000 : ℝ)*(X 1 0+X 2 0)+(61125151299/33762500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (1080032764801861697/1080400000000000000 : ℝ)) (alpha := (61125151299/33762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1080032764801861697/1080400000000000000 : ℝ)*(X 0 1+X 2 1)+(61125151299/33762500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (1080032764801861697/1080400000000000000 : ℝ)) (alpha := (61125151299/33762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1080032764801861697/1080400000000000000 : ℝ)*(X 0 2+X 1 2)+(61125151299/33762500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (1080032764801861697/1080400000000000000 : ℝ)) (alpha := (61125151299/33762500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2044463387/10000000000 : ℝ)*X 0 0+(1344112369/2500000000 : ℝ)*X 0 1+(2688224653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295890937/10000000000 : ℝ)*X 1 0+(-2153689163/10000000000 : ℝ)*X 1 1+(3360281/6250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295891617/10000000000 : ℝ)*X 2 0+(5376449267/10000000000 : ℝ)*X 2 1+(-2153688701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4473733733/10000000000 : ℝ)*X 0 0+(862875499/2000000000 : ℝ)*X 0 1+(4314377393/10000000000 : ℝ)*X 0 2+(4473733733/10000000000 : ℝ)*X 1 0+(862875499/2000000000 : ℝ)*X 1 1+(4314377393/10000000000 : ℝ)*X 1 2+(4473733733/10000000000 : ℝ)*X 2 0+(862875499/2000000000 : ℝ)*X 2 1+(4314377393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-287535771/1250000000 : ℝ)*X 0 0+(2640507109/5000000000 : ℝ)*X 0 1+(5281013003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340832983/2500000000 : ℝ)*X 1 0+(-2191200413/10000000000 : ℝ)*X 1 1+(2640506817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363331713/10000000000 : ℝ)*X 2 0+(2640506933/5000000000 : ℝ)*X 2 1+(-1095600199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((425808149/1000000000 : ℝ)*X 0 0+(4422182839/10000000000 : ℝ)*X 0 1+(884436491/2000000000 : ℝ)*X 0 2+(425808149/1000000000 : ℝ)*X 1 0+(4422182839/10000000000 : ℝ)*X 1 1+(884436491/2000000000 : ℝ)*X 1 2+(425808149/1000000000 : ℝ)*X 2 0+(4422182839/10000000000 : ℝ)*X 2 1+(884436491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-56170033/250000000 : ℝ)*X 0 0+(208645083/400000000 : ℝ)*X 0 1+(2693028423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528909871/1000000000 : ℝ)*X 1 0+(-85993731/400000000 : ℝ)*X 1 1+(215442273/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644549337/5000000000 : ℝ)*X 2 0+(2693028463/5000000000 : ℝ)*X 2 1+(-537460797/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4495170077/10000000000 : ℝ)*X 0 0+(4303518719/10000000000 : ℝ)*X 0 1+(4303518781/10000000000 : ℝ)*X 0 2+(4495170077/10000000000 : ℝ)*X 1 0+(4303518719/10000000000 : ℝ)*X 1 1+(4303518781/10000000000 : ℝ)*X 1 2+(4495170077/10000000000 : ℝ)*X 2 0+(4303518719/10000000000 : ℝ)*X 2 1+(4303518781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2098273911/10000000000 : ℝ)*X 0 0+(5440050789/10000000000 : ℝ)*X 0 1+(2636489921/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369007053/10000000000 : ℝ)*X 1 0+(-34285951/156250000 : ℝ)*X 1 1+(5272979383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684503357/5000000000 : ℝ)*X 2 0+(5272980019/10000000000 : ℝ)*X 2 1+(-274287559/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1059924447/2500000000 : ℝ)*X 0 0+(4431252479/10000000000 : ℝ)*X 0 1+(4431252227/10000000000 : ℝ)*X 0 2+(1059924447/2500000000 : ℝ)*X 1 0+(4431252479/10000000000 : ℝ)*X 1 1+(4431252227/10000000000 : ℝ)*X 1 2+(1059924447/2500000000 : ℝ)*X 2 0+(4431252479/10000000000 : ℝ)*X 2 1+(4431252227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6223/10000 : ℝ) ≤ (-16807621263608998062660615674301/27010000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2801843/6250000000000 : ℝ)*(lower0) + (2813807/100000000000000 : ℝ)*(upper1) + (10799771/10000000000000 : ℝ)*(lower5) + (3912320828148689/100000000000000 : ℝ)*(major0) + (3912320828148689/100000000000000 : ℝ)*(major1) + (3912320828148689/100000000000000 : ℝ)*(major2) + (5007771653/100000000000000 : ℝ)*(sp1) + (1712718603/25000000000000 : ℝ)*(sp3) + (5224530227202201/100000000000000 : ℝ)*(sp4) + (1044912284217209/20000000000000 : ℝ)*(sp5) + (5224424322989537/100000000000000 : ℝ)*(sp6) + (1310405421939059/50000000000000 : ℝ)*(sp7) + (36201655497/100000000000000 : ℝ)*(sp8) + (142105868161/100000000000000 : ℝ)*(sp14) + (262081769475253/10000000000000 : ℝ)*(f.failure) + (2612283214428849/50000000000000 : ℝ)*(f.sum) + (315369278247/844062500000000000000000000 : ℝ)*base66 + (2438265035252817233/108040000000000000000000000000000 : ℝ)*base67 + (2147821167020622767/108040000000000000000000000000000 : ℝ)*base70 + (121518428546462767/108040000000000000000000000000000 : ℝ)*base72 + (21670869313251/6752500000000000000000000000 : ℝ)*base74 + (1656641536611222767/108040000000000000000000000000000 : ℝ)*base76 + (14647641099822767/108040000000000000000000000000000 : ℝ)*base78 + (965537326411502767/108040000000000000000000000000000 : ℝ)*base80 + (8865776738919/1688125000000000000000000000 : ℝ)*base82 + (5169149/1000000000000000000000 : ℝ)*base89 + (5169149/1000000000000000000000 : ℝ)*base91 + (5169149/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59291/100000 : ℝ) ≤ (16015123294314333133336478094327/27010000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26465233/50000000000000 : ℝ)*(upper0) + (31850133/25000000000000 : ℝ)*(lower1) + (52863403/12500000000000 : ℝ)*(upper4) + (3976302721458403/100000000000000 : ℝ)*(major0) + (3976302721458403/100000000000000 : ℝ)*(major1) + (3976302721458403/100000000000000 : ℝ)*(major2) + (5269152228709957/100000000000000 : ℝ)*(sp0) + (5269160754156873/100000000000000 : ℝ)*(sp1) + (5269151174643191/100000000000000 : ℝ)*(sp2) + (53273332311931/2000000000000 : ℝ)*(sp3) + (1839427527/100000000000000 : ℝ)*(sp5) + (1141894121/10000000000000 : ℝ)*(sp6) + (5898372109/50000000000000 : ℝ)*(sp7) + (10364874443/100000000000000 : ℝ)*(sp8) + (83239950385649/3125000000000 : ℝ)*(f.failure) + (13172906483961/250000000000 : ℝ)*(f.sum) + (30638159348779/13505000000000000000000000000 : ℝ)*base66 + (1162646892712033891/108040000000000000000000000000000 : ℝ)*base67 + (239779513678006109/108040000000000000000000000000000 : ℝ)*base70 + (4954620134993891/108040000000000000000000000000000 : ℝ)*base71 + (134942617654517/6752500000000000000000000000 : ℝ)*base74 + (432069679046073891/108040000000000000000000000000000 : ℝ)*base75 + (253147304822513891/108040000000000000000000000000000 : ℝ)*base77 + (437608592628033891/108040000000000000000000000000000 : ℝ)*base79 + (75390054578131/13505000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3837183/312500000000000000000 : ℝ)*base90 + (3837183/312500000000000000000 : ℝ)*base92 + (3837183/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39889/50000 : ℝ) ≤ (10774301361214772536978803867/13505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21286867/100000000000000 : ℝ)*(upper0) + (4193301/20000000000000 : ℝ)*(lower3) + (6805817/25000000000000 : ℝ)*(upper4) + (138883518686729/3125000000000 : ℝ)*(major0) + (138883518686729/3125000000000 : ℝ)*(major1) + (138883518686729/3125000000000 : ℝ)*(major2) + (1201309987/5000000000000 : ℝ)*(sp1) + (95286590227/100000000000000 : ℝ)*(sp2) + (19642865207/100000000000000 : ℝ)*(sp3) + (1377906239/100000000000000 : ℝ)*(sp4) + (735598065899441/12500000000000 : ℝ)*(sp8) + (5884761878902027/100000000000000 : ℝ)*(sp9) + (294234530925577/5000000000000 : ℝ)*(sp10) + (1488573142070059/50000000000000 : ℝ)*(sp11) + (1488582963502663/50000000000000 : ℝ)*(f.failure) + (5884785905101767/100000000000000 : ℝ)*(f.sum) + (93164625802551/13505000000000000000000000000 : ℝ)*base65 + (14807182791995137/3376250000000000000000000000000 : ℝ)*base68 + (2116203128748613/3376250000000000000000000000000 : ℝ)*base69 + (10062590866807363/3376250000000000000000000000000 : ℝ)*base71 + (189311355787367/6752500000000000000000000000 : ℝ)*base74 + (17580764654838887/3376250000000000000000000000000 : ℝ)*base76 + (6985870054596113/3376250000000000000000000000000 : ℝ)*base77 + (177075878754303887/3376250000000000000000000000000 : ℝ)*base80 + (2389704518633/6752500000000000000000000000 : ℝ)*base81 + (24499679/5000000000000000000000 : ℝ)*base89 + (24499679/5000000000000000000000 : ℝ)*base91 + (24499679/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41551/50000 : ℝ) ≤ (-1402822605124832844590792369073/1688125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67807033/100000000000000 : ℝ)*(lower0) + (1307811/100000000000000 : ℝ)*(lower1) + (1720613/2000000000000 : ℝ)*(lower2) + (33831181/50000000000000 : ℝ)*(upper5) + (139973774027947/3125000000000 : ℝ)*(major0) + (139973774027947/3125000000000 : ℝ)*(major1) + (139973774027947/3125000000000 : ℝ)*(major2) + (12854795839/100000000000000 : ℝ)*(sp0) + (254565995739/50000000000000 : ℝ)*(sp5) + (32350653259/100000000000000 : ℝ)*(sp7) + (2992735698851727/50000000000000 : ℝ)*(sp12) + (1196995024101563/20000000000000 : ℝ)*(sp13) + (5985484252499293/100000000000000 : ℝ)*(sp14) + (1500252375797597/50000000000000 : ℝ)*(sp15) + (1500268551124227/50000000000000 : ℝ)*(f.failure) + (5985484252499293/100000000000000 : ℝ)*(f.sum) + (60850093867193/13505000000000000000000000000 : ℝ)*base65 + (26031786986879191/3376250000000000000000000000000 : ℝ)*base68 + (12734480678989191/3376250000000000000000000000000 : ℝ)*base70 + (7209658065474191/3376250000000000000000000000000 : ℝ)*base72 + (299405058713403/13505000000000000000000000000 : ℝ)*base73 + (5915326066392059/3376250000000000000000000000000 : ℝ)*base75 + (9633242761762059/3376250000000000000000000000000 : ℝ)*base77 + (67901915815500441/3376250000000000000000000000000 : ℝ)*base80 + (99302473974733/13505000000000000000000000000 : ℝ)*base81 + (19741691/5000000000000000000000 : ℝ)*base89 + (19741691/5000000000000000000000 : ℝ)*base91 + (19741691/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1132_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59291/100000 : ℝ) else (39889/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41551/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1132_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1132_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59291/100000 : ℝ) else (39889/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41551/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1132_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1132_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59291/100000 : ℝ) else (39889/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41551/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
