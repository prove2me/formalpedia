-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1600_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:34.487223+00:00
-- url     : https://prove2.me/submissions/500b252c-d373-442b-9db9-d440aaa4cbb2

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
theorem support_rectangle_w1600_s6_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354954519/10000000000 : ℝ)*x 0 + (-375122107/2000000000 : ℝ)*x 1 + (5179821209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354954519/10000000000 : ℝ)^4719 ≤ (11259666959807/25000000000000 : ℝ)^3695 := by
    have hnat : (5354954519 : ℕ)^4719*25000000000000^3695 ≤ 11259666959807^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354954519 10000000000 11259666959807 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375122107/2000000000 : ℝ)^4719 ≤ (11795266970813/100000000000000 : ℝ)^3695 := by
    have hnat : (375122107 : ℕ)^4719*100000000000000^3695 ≤ 11795266970813^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375122107 2000000000 11795266970813 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179821209/10000000000 : ℝ)^4719 ≤ (43166065172241/100000000000000 : ℝ)^3695 := by
    have hnat : (5179821209 : ℕ)^4719*100000000000000^3695 ≤ 43166065172241^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179821209 10000000000 43166065172241 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354954519/10000000000 : ℝ), (-375122107/2000000000 : ℝ), (5179821209/10000000000 : ℝ)] ![(11259666959807/25000000000000 : ℝ), (11795266970813/100000000000000 : ℝ), (43166065172241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354954519/10000000000 : ℝ)|^4719 ≤ (11259666959807/25000000000000 : ℝ)^3695
        have hw : |(5354954519/10000000000 : ℝ)|=(5354954519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375122107/2000000000 : ℝ)|^4719 ≤ (11795266970813/100000000000000 : ℝ)^3695
        have hw : |(-375122107/2000000000 : ℝ)|=(375122107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179821209/10000000000 : ℝ)|^4719 ≤ (43166065172241/100000000000000 : ℝ)^3695
        have hw : |(5179821209/10000000000 : ℝ)|=(5179821209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s6_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1729858067/10000000000 : ℝ)*x 0 + (2590956051/5000000000 : ℝ)*x 1 + (1365095331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1729858067/10000000000 : ℝ)^4719 ≤ (10637494637141/100000000000000 : ℝ)^3695 := by
    have hnat : (1729858067 : ℕ)^4719*100000000000000^3695 ≤ 10637494637141^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729858067 10000000000 10637494637141 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590956051/5000000000 : ℝ)^4719 ≤ (43188319748243/100000000000000 : ℝ)^3695 := by
    have hnat : (2590956051 : ℕ)^4719*100000000000000^3695 ≤ 43188319748243^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590956051 5000000000 43188319748243 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365095331/2500000000 : ℝ)^4719 ≤ (721471649991/1562500000000 : ℝ)^3695 := by
    have hnat : (1365095331 : ℕ)^4719*1562500000000^3695 ≤ 721471649991^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365095331 2500000000 721471649991 1562500000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1729858067/10000000000 : ℝ), (2590956051/5000000000 : ℝ), (1365095331/2500000000 : ℝ)] ![(10637494637141/100000000000000 : ℝ), (43188319748243/100000000000000 : ℝ), (721471649991/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1729858067/10000000000 : ℝ)|^4719 ≤ (10637494637141/100000000000000 : ℝ)^3695
        have hw : |(-1729858067/10000000000 : ℝ)|=(1729858067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590956051/5000000000 : ℝ)|^4719 ≤ (43188319748243/100000000000000 : ℝ)^3695
        have hw : |(2590956051/5000000000 : ℝ)|=(2590956051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365095331/2500000000 : ℝ)|^4719 ≤ (721471649991/1562500000000 : ℝ)^3695
        have hw : |(1365095331/2500000000 : ℝ)|=(1365095331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s6_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640012551/5000000000 : ℝ)*x 0 + (-797525247/5000000000 : ℝ)*x 1 + (2730190689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640012551/5000000000 : ℝ)^4719 ≤ (44235378669649/100000000000000 : ℝ)^3695 := by
    have hnat : (2640012551 : ℕ)^4719*100000000000000^3695 ≤ 44235378669649^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640012551 5000000000 44235378669649 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (797525247/5000000000 : ℝ)^4719 ≤ (959043512971/10000000000000 : ℝ)^3695 := by
    have hnat : (797525247 : ℕ)^4719*10000000000000^3695 ≤ 959043512971^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797525247 5000000000 959043512971 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730190689/5000000000 : ℝ)^4719 ≤ (2885886636413/6250000000000 : ℝ)^3695 := by
    have hnat : (2730190689 : ℕ)^4719*6250000000000^3695 ≤ 2885886636413^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730190689 5000000000 2885886636413 6250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640012551/5000000000 : ℝ), (-797525247/5000000000 : ℝ), (2730190689/5000000000 : ℝ)] ![(44235378669649/100000000000000 : ℝ), (959043512971/10000000000000 : ℝ), (2885886636413/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640012551/5000000000 : ℝ)|^4719 ≤ (44235378669649/100000000000000 : ℝ)^3695
        have hw : |(2640012551/5000000000 : ℝ)|=(2640012551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-797525247/5000000000 : ℝ)|^4719 ≤ (959043512971/10000000000000 : ℝ)^3695
        have hw : |(-797525247/5000000000 : ℝ)|=(797525247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730190689/5000000000 : ℝ)|^4719 ≤ (2885886636413/6250000000000 : ℝ)^3695
        have hw : |(2730190689/5000000000 : ℝ)|=(2730190689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s6_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280025159/10000000000 : ℝ)*x 0 + (2730190643/5000000000 : ℝ)*x 1 + (-319010109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280025159/10000000000 : ℝ)^4719 ≤ (5529422409941/12500000000000 : ℝ)^3695 := by
    have hnat : (5280025159 : ℕ)^4719*12500000000000^3695 ≤ 5529422409941^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280025159 10000000000 5529422409941 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730190643/5000000000 : ℝ)^4719 ≤ (11543546297259/25000000000000 : ℝ)^3695 := by
    have hnat : (2730190643 : ℕ)^4719*25000000000000^3695 ≤ 11543546297259^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730190643 5000000000 11543546297259 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319010109/2000000000 : ℝ)^4719 ≤ (1918087104267/20000000000000 : ℝ)^3695 := by
    have hnat : (319010109 : ℕ)^4719*20000000000000^3695 ≤ 1918087104267^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319010109 2000000000 1918087104267 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280025159/10000000000 : ℝ), (2730190643/5000000000 : ℝ), (-319010109/2000000000 : ℝ)] ![(5529422409941/12500000000000 : ℝ), (11543546297259/25000000000000 : ℝ), (1918087104267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280025159/10000000000 : ℝ)|^4719 ≤ (5529422409941/12500000000000 : ℝ)^3695
        have hw : |(5280025159/10000000000 : ℝ)|=(5280025159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730190643/5000000000 : ℝ)|^4719 ≤ (11543546297259/25000000000000 : ℝ)^3695
        have hw : |(2730190643/5000000000 : ℝ)|=(2730190643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319010109/2000000000 : ℝ)|^4719 ≤ (1918087104267/20000000000000 : ℝ)^3695
        have hw : |(-319010109/2000000000 : ℝ)|=(319010109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s6_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4221046667/10000000000 : ℝ)*x 0 + (71397313/156250000 : ℝ)*x 1 + (1947068089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221046667/10000000000 : ℝ)^4719 ≤ (3323627696931/10000000000000 : ℝ)^3695 := by
    have hnat : (4221046667 : ℕ)^4719*10000000000000^3695 ≤ 3323627696931^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221046667 10000000000 3323627696931 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71397313/156250000 : ℝ)^4719 ≤ (9194729016793/25000000000000 : ℝ)^3695 := by
    have hnat : (71397313 : ℕ)^4719*25000000000000^3695 ≤ 9194729016793^3695*156250000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71397313 156250000 9194729016793 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947068089/5000000000 : ℝ)^4719 ≤ (29984806947999/100000000000000 : ℝ)^3695 := by
    have hnat : (1947068089 : ℕ)^4719*100000000000000^3695 ≤ 29984806947999^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947068089 5000000000 29984806947999 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221046667/10000000000 : ℝ), (71397313/156250000 : ℝ), (1947068089/5000000000 : ℝ)] ![(3323627696931/10000000000000 : ℝ), (9194729016793/25000000000000 : ℝ), (29984806947999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221046667/10000000000 : ℝ)|^4719 ≤ (3323627696931/10000000000000 : ℝ)^3695
        have hw : |(4221046667/10000000000 : ℝ)|=(4221046667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71397313/156250000 : ℝ)|^4719 ≤ (9194729016793/25000000000000 : ℝ)^3695
        have hw : |(71397313/156250000 : ℝ)|=(71397313/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1947068089/5000000000 : ℝ)|^4719 ≤ (29984806947999/100000000000000 : ℝ)^3695
        have hw : |(1947068089/5000000000 : ℝ)|=(1947068089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (324/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16357/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (324/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (324/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (324/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (324/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (324/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (324/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (324/3125 : ℝ) ^ (4715/1024 : ℝ) ≤ (1468064946166769/50000000000000000000 : ℝ) := by
    have hpowers : (324/3125 : ℝ)^4715 ≤ (1468064946166769/50000000000000000000 : ℝ)^1024 := by
      have hnat : (324 : ℕ)^4715*50000000000000000000^1024 ≤ 1468064946166769^1024*3125^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        324 3125 1468064946166769 50000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (324/3125 : ℝ)) (X := (1468064946166769/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8179/50000 : ℝ) ^ (4715/1024 : ℝ) ≤ (2995965992870823/12500000000000000000 : ℝ) := by
    have hpowers : (8179/50000 : ℝ)^4715 ≤ (2995965992870823/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8179 : ℕ)^4715*12500000000000000000^1024 ≤ 2995965992870823^1024*50000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8179 50000 2995965992870823 12500000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8179/50000 : ℝ)) (X := (2995965992870823/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001468064946166769/25000000000000000000 : ℝ) ≤ (10000127530345987/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (25001468064946166769/25000000000000000000 : ℝ)^1024 ≤ (10000127530345987/10000000000000000 : ℝ)^4715 := by
      have hnat : (25001468064946166769 : ℕ)^1024*10000000000000000^4715 ≤ 10000127530345987^4715*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001468064946166769 25000000000000000000 10000127530345987 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000127530345987/10000000000000000 : ℝ)) (X := (25001468064946166769/25000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013451928917650061/50000000000000000000 : ℝ) ≤ (625036514647131/625000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (50013451928917650061/50000000000000000000 : ℝ)^1024 ≤ (625036514647131/625000000000000 : ℝ)^4715 := by
      have hnat : (50013451928917650061 : ℕ)^1024*625000000000000^4715 ≤ 625036514647131^4715*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013451928917650061 50000000000000000000 625036514647131 625000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625036514647131/625000000000000 : ℝ)) (X := (50013451928917650061/50000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252995965992870823/6250000000000000000 : ℝ) ≤ (2000208187672441/2000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (6252995965992870823/6250000000000000000 : ℝ)^1024 ≤ (2000208187672441/2000000000000000 : ℝ)^4715 := by
      have hnat : (6252995965992870823 : ℕ)^1024*2000000000000000^4715 ≤ 2000208187672441^4715*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252995965992870823 6250000000000000000 2000208187672441 2000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000208187672441/2000000000000000 : ℝ)) (X := (6252995965992870823/6250000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1468064946166769/50000000000000000000 : ℝ) ≤ ((29945646846230156953/29950000000000000000 : ℝ)+2*(456704008109/599000000000000 : ℝ)*(324/3125 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (29945646846230156953/29950000000000000000 : ℝ)+2*(456704008109/599000000000000 : ℝ)*(324/3125 : ℝ)=(10000127530345987/10000000000000000 : ℝ) by norm_num, show 1+2*(1468064946166769/50000000000000000000 : ℝ)=(25001468064946166769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2995965992870823/12500000000000000000 : ℝ)+(1468064946166769/50000000000000000000 : ℝ) ≤ ((29945646846230156953/29950000000000000000 : ℝ)+(456704008109/599000000000000 : ℝ)*((8179/50000 : ℝ)+(324/3125 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (29945646846230156953/29950000000000000000 : ℝ)+(456704008109/599000000000000 : ℝ)*((8179/50000 : ℝ)+(324/3125 : ℝ))=(625036514647131/625000000000000 : ℝ) by norm_num, show 1+(2995965992870823/12500000000000000000 : ℝ)+(1468064946166769/50000000000000000000 : ℝ)=(50013451928917650061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2995965992870823/12500000000000000000 : ℝ) ≤ ((29945646846230156953/29950000000000000000 : ℝ)+2*(456704008109/599000000000000 : ℝ)*(8179/50000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (29945646846230156953/29950000000000000000 : ℝ)+2*(456704008109/599000000000000 : ℝ)*(8179/50000 : ℝ)=(2000208187672441/2000000000000000 : ℝ) by norm_num, show 1+2*(2995965992870823/12500000000000000000 : ℝ)=(6252995965992870823/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29945646846230156953/29950000000000000000 : ℝ)*(X 1 0+X 2 0)+(456704008109/599000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (29945646846230156953/29950000000000000000 : ℝ)) (alpha := (456704008109/599000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29945646846230156953/29950000000000000000 : ℝ)*(X 0 1+X 2 1)+(456704008109/599000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (29945646846230156953/29950000000000000000 : ℝ)) (alpha := (456704008109/599000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29945646846230156953/29950000000000000000 : ℝ)*(X 0 2+X 1 2)+(456704008109/599000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (29945646846230156953/29950000000000000000 : ℝ)) (alpha := (456704008109/599000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5354954519/10000000000 : ℝ)*X 1 0+(-375122107/2000000000 : ℝ)*X 1 1+(5179821209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s6_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1729858067/10000000000 : ℝ)*X 0 0+(2590956051/5000000000 : ℝ)*X 0 1+(1365095331/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2640012551/5000000000 : ℝ)*X 1 0+(-797525247/5000000000 : ℝ)*X 1 1+(2730190689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5280025159/10000000000 : ℝ)*X 2 0+(2730190643/5000000000 : ℝ)*X 2 1+(-319010109/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4221046667/10000000000 : ℝ)*X 0 0+(71397313/156250000 : ℝ)*X 0 1+(1947068089/5000000000 : ℝ)*X 0 2+(4221046667/10000000000 : ℝ)*X 1 0+(71397313/156250000 : ℝ)*X 1 1+(1947068089/5000000000 : ℝ)*X 1 2+(4221046667/10000000000 : ℝ)*X 2 0+(71397313/156250000 : ℝ)*X 2 1+(1947068089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2289011962561881438658567977/748750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (325810471/100000000000000 : ℝ)*(base19) + (110726607/25000000000000 : ℝ)*(base23) + (61822229/50000000000000 : ℝ)*(lower1) + (33356373/100000000000000 : ℝ)*(upper3) + (8821561/20000000000000 : ℝ)*(lower4) + (1924931/2500000000000 : ℝ)*(upper5) + (1267974037910603/50000000000000 : ℝ)*(major0) + (1267974037910603/50000000000000 : ℝ)*(major1) + (1267974037910603/50000000000000 : ℝ)*(major2) + (366994577/100000000000000 : ℝ)*(sp0) + (3591057168272143/100000000000000 : ℝ)*(sp1) + (448882059433387/12500000000000 : ℝ)*(sp2) + (718211345073143/20000000000000 : ℝ)*(sp3) + (1480838881466561/100000000000000 : ℝ)*(sp4) + (1480838881466561/100000000000000 : ℝ)*(f.failure) + (3591057168272143/100000000000000 : ℝ)*(f.sum) + (43851163145123/14975000000000000000000000000 : ℝ)*base66 + (758486072795777341/1497500000000000000000000000000000 : ℝ)*base68 + (1466516420834222659/1497500000000000000000000000000000 : ℝ)*base69 + (239268236535777341/1497500000000000000000000000000000 : ℝ)*base72 + (8248680352431/1871875000000000000000000000 : ℝ)*base74 + (3619090241293277341/1497500000000000000000000000000000 : ℝ)*base76 + (5651392959539222659/1497500000000000000000000000000000 : ℝ)*base77 + (5926111341535777341/1497500000000000000000000000000000 : ℝ)*base80 + (3140975842849/7487500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1337333/1250000000000000000000 : ℝ)*base90 + (1337333/1250000000000000000000 : ℝ)*base92 + (1337333/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1600_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16357/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1600_box_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-363089261/2500000000 : ℝ)*x 0 + (1084133059/2000000000 : ℝ)*x 1 + (5420666453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363089261/2500000000 : ℝ)^4719 ≤ (8508592821209/100000000000000 : ℝ)^3695 := by
    have hnat : (363089261 : ℕ)^4719*100000000000000^3695 ≤ 8508592821209^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363089261 2500000000 8508592821209 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084133059/2000000000 : ℝ)^4719 ≤ (5718212167317/12500000000000 : ℝ)^3695 := by
    have hnat : (1084133059 : ℕ)^4719*12500000000000^3695 ≤ 5718212167317^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084133059 2000000000 5718212167317 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420666453/10000000000 : ℝ)^4719 ≤ (22872854909659/50000000000000 : ℝ)^3695 := by
    have hnat : (5420666453 : ℕ)^4719*50000000000000^3695 ≤ 22872854909659^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420666453 10000000000 22872854909659 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-363089261/2500000000 : ℝ), (1084133059/2000000000 : ℝ), (5420666453/10000000000 : ℝ)] ![(8508592821209/100000000000000 : ℝ), (5718212167317/12500000000000 : ℝ), (22872854909659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-363089261/2500000000 : ℝ)|^4719 ≤ (8508592821209/100000000000000 : ℝ)^3695
        have hw : |(-363089261/2500000000 : ℝ)|=(363089261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084133059/2000000000 : ℝ)|^4719 ≤ (5718212167317/12500000000000 : ℝ)^3695
        have hw : |(1084133059/2000000000 : ℝ)|=(1084133059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420666453/10000000000 : ℝ)|^4719 ≤ (22872854909659/50000000000000 : ℝ)^3695
        have hw : |(5420666453/10000000000 : ℝ)|=(5420666453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625502547/5000000000 : ℝ)*x 0 + (-211309301/1250000000 : ℝ)*x 1 + (1084133347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625502547/5000000000 : ℝ)^4719 ≤ (21962555862871/50000000000000 : ℝ)^3695 := by
    have hnat : (2625502547 : ℕ)^4719*50000000000000^3695 ≤ 21962555862871^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625502547 5000000000 21962555862871 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211309301/1250000000 : ℝ)^4719 ≤ (5164587700549/50000000000000 : ℝ)^3695 := by
    have hnat : (211309301 : ℕ)^4719*50000000000000^3695 ≤ 5164587700549^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211309301 1250000000 5164587700549 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084133347/2000000000 : ℝ)^4719 ≤ (45745712858679/100000000000000 : ℝ)^3695 := by
    have hnat : (1084133347 : ℕ)^4719*100000000000000^3695 ≤ 45745712858679^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084133347 2000000000 45745712858679 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625502547/5000000000 : ℝ), (-211309301/1250000000 : ℝ), (1084133347/2000000000 : ℝ)] ![(21962555862871/50000000000000 : ℝ), (5164587700549/50000000000000 : ℝ), (45745712858679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625502547/5000000000 : ℝ)|^4719 ≤ (21962555862871/50000000000000 : ℝ)^3695
        have hw : |(2625502547/5000000000 : ℝ)|=(2625502547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211309301/1250000000 : ℝ)|^4719 ≤ (5164587700549/50000000000000 : ℝ)^3695
        have hw : |(-211309301/1250000000 : ℝ)|=(211309301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084133347/2000000000 : ℝ)|^4719 ≤ (45745712858679/100000000000000 : ℝ)^3695
        have hw : |(1084133347/2000000000 : ℝ)|=(1084133347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251006623/10000000000 : ℝ)*x 0 + (1355166427/2500000000 : ℝ)*x 1 + (-845236867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251006623/10000000000 : ℝ)^4719 ≤ (43925128060529/100000000000000 : ℝ)^3695 := by
    have hnat : (5251006623 : ℕ)^4719*100000000000000^3695 ≤ 43925128060529^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251006623 10000000000 43925128060529 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355166427/2500000000 : ℝ)^4719 ≤ (45745701789799/100000000000000 : ℝ)^3695 := by
    have hnat : (1355166427 : ℕ)^4719*100000000000000^3695 ≤ 45745701789799^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355166427 2500000000 45745701789799 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845236867/5000000000 : ℝ)^4719 ≤ (10329170141501/100000000000000 : ℝ)^3695 := by
    have hnat : (845236867 : ℕ)^4719*100000000000000^3695 ≤ 10329170141501^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845236867 5000000000 10329170141501 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251006623/10000000000 : ℝ), (1355166427/2500000000 : ℝ), (-845236867/5000000000 : ℝ)] ![(43925128060529/100000000000000 : ℝ), (45745701789799/100000000000000 : ℝ), (10329170141501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251006623/10000000000 : ℝ)|^4719 ≤ (43925128060529/100000000000000 : ℝ)^3695
        have hw : |(5251006623/10000000000 : ℝ)|=(5251006623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355166427/2500000000 : ℝ)|^4719 ≤ (45745701789799/100000000000000 : ℝ)^3695
        have hw : |(1355166427/2500000000 : ℝ)|=(1355166427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-845236867/5000000000 : ℝ)|^4719 ≤ (10329170141501/100000000000000 : ℝ)^3695
        have hw : |(-845236867/5000000000 : ℝ)|=(845236867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4501627443/10000000000 : ℝ)*x 0 + (4093421867/10000000000 : ℝ)*x 1 + (51167799/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4501627443/10000000000 : ℝ)^4719 ≤ (36083397018419/100000000000000 : ℝ)^3695 := by
    have hnat : (4501627443 : ℕ)^4719*100000000000000^3695 ≤ 36083397018419^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501627443 10000000000 36083397018419 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4093421867/10000000000 : ℝ)^4719 ≤ (31958291242681/100000000000000 : ℝ)^3695 := by
    have hnat : (4093421867 : ℕ)^4719*100000000000000^3695 ≤ 31958291242681^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093421867 10000000000 31958291242681 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51167799/125000000 : ℝ)^4719 ≤ (3994788964107/12500000000000 : ℝ)^3695 := by
    have hnat : (51167799 : ℕ)^4719*12500000000000^3695 ≤ 3994788964107^3695*125000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51167799 125000000 3994788964107 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4501627443/10000000000 : ℝ), (4093421867/10000000000 : ℝ), (51167799/125000000 : ℝ)] ![(36083397018419/100000000000000 : ℝ), (31958291242681/100000000000000 : ℝ), (3994788964107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4501627443/10000000000 : ℝ)|^4719 ≤ (36083397018419/100000000000000 : ℝ)^3695
        have hw : |(4501627443/10000000000 : ℝ)|=(4501627443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4093421867/10000000000 : ℝ)|^4719 ≤ (31958291242681/100000000000000 : ℝ)^3695
        have hw : |(4093421867/10000000000 : ℝ)|=(4093421867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51167799/125000000 : ℝ)|^4719 ≤ (3994788964107/12500000000000 : ℝ)^3695
        have hw : |(51167799/125000000 : ℝ)|=(51167799/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2017998423/10000000000 : ℝ)*x 0 + (2606741819/5000000000 : ℝ)*x 1 + (2606742093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017998423/10000000000 : ℝ)^4719 ≤ (6475341235429/50000000000000 : ℝ)^3695 := by
    have hnat : (2017998423 : ℕ)^4719*50000000000000^3695 ≤ 6475341235429^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017998423 10000000000 6475341235429 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606741819/5000000000 : ℝ)^4719 ≤ (43524655834151/100000000000000 : ℝ)^3695 := by
    have hnat : (2606741819 : ℕ)^4719*100000000000000^3695 ≤ 43524655834151^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606741819 5000000000 43524655834151 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606742093/5000000000 : ℝ)^4719 ≤ (43524661676983/100000000000000 : ℝ)^3695 := by
    have hnat : (2606742093 : ℕ)^4719*100000000000000^3695 ≤ 43524661676983^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606742093 5000000000 43524661676983 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2017998423/10000000000 : ℝ), (2606741819/5000000000 : ℝ), (2606742093/5000000000 : ℝ)] ![(6475341235429/50000000000000 : ℝ), (43524655834151/100000000000000 : ℝ), (43524661676983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2017998423/10000000000 : ℝ)|^4719 ≤ (6475341235429/50000000000000 : ℝ)^3695
        have hw : |(-2017998423/10000000000 : ℝ)|=(2017998423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606741819/5000000000 : ℝ)|^4719 ≤ (43524655834151/100000000000000 : ℝ)^3695
        have hw : |(2606741819/5000000000 : ℝ)|=(2606741819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606742093/5000000000 : ℝ)|^4719 ≤ (43524661676983/100000000000000 : ℝ)^3695
        have hw : |(2606742093/5000000000 : ℝ)|=(2606742093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394201267/10000000000 : ℝ)*x 0 + (-222212827/1250000000 : ℝ)*x 1 + (5213484227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394201267/10000000000 : ℝ)^4719 ≤ (2273033224863/5000000000000 : ℝ)^3695 := by
    have hnat : (5394201267 : ℕ)^4719*5000000000000^3695 ≤ 2273033224863^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394201267 10000000000 2273033224863 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222212827/1250000000 : ℝ)^4719 ≤ (2202934673933/20000000000000 : ℝ)^3695 := by
    have hnat : (222212827 : ℕ)^4719*20000000000000^3695 ≤ 2202934673933^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222212827 1250000000 2202934673933 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213484227/10000000000 : ℝ)^4719 ≤ (4352466211413/10000000000000 : ℝ)^3695 := by
    have hnat : (5213484227 : ℕ)^4719*10000000000000^3695 ≤ 4352466211413^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213484227 10000000000 4352466211413 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394201267/10000000000 : ℝ), (-222212827/1250000000 : ℝ), (5213484227/10000000000 : ℝ)] ![(2273033224863/5000000000000 : ℝ), (2202934673933/20000000000000 : ℝ), (4352466211413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394201267/10000000000 : ℝ)|^4719 ≤ (2273033224863/5000000000000 : ℝ)^3695
        have hw : |(5394201267/10000000000 : ℝ)|=(5394201267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222212827/1250000000 : ℝ)|^4719 ≤ (2202934673933/20000000000000 : ℝ)^3695
        have hw : |(-222212827/1250000000 : ℝ)|=(222212827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213484227/10000000000 : ℝ)|^4719 ≤ (4352466211413/10000000000000 : ℝ)^3695
        have hw : |(5213484227/10000000000 : ℝ)|=(5213484227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697101139/5000000000 : ℝ)*x 0 + (1303370707/2500000000 : ℝ)*x 1 + (-1777703127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697101139/5000000000 : ℝ)^4719 ≤ (11365168844731/25000000000000 : ℝ)^3695 := by
    have hnat : (2697101139 : ℕ)^4719*25000000000000^3695 ≤ 11365168844731^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697101139 5000000000 11365168844731 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303370707/2500000000 : ℝ)^4719 ≤ (5440580899731/12500000000000 : ℝ)^3695 := by
    have hnat : (1303370707 : ℕ)^4719*12500000000000^3695 ≤ 5440580899731^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303370707 2500000000 5440580899731 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777703127/10000000000 : ℝ)^4719 ≤ (1376834676659/12500000000000 : ℝ)^3695 := by
    have hnat : (1777703127 : ℕ)^4719*12500000000000^3695 ≤ 1376834676659^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777703127 10000000000 1376834676659 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697101139/5000000000 : ℝ), (1303370707/2500000000 : ℝ), (-1777703127/10000000000 : ℝ)] ![(11365168844731/25000000000000 : ℝ), (5440580899731/12500000000000 : ℝ), (1376834676659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697101139/5000000000 : ℝ)|^4719 ≤ (11365168844731/25000000000000 : ℝ)^3695
        have hw : |(2697101139/5000000000 : ℝ)|=(2697101139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303370707/2500000000 : ℝ)|^4719 ≤ (5440580899731/12500000000000 : ℝ)^3695
        have hw : |(1303370707/2500000000 : ℝ)|=(1303370707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777703127/10000000000 : ℝ)|^4719 ≤ (1376834676659/12500000000000 : ℝ)^3695
        have hw : |(-1777703127/10000000000 : ℝ)|=(1777703127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (786882093/2000000000 : ℝ)*x 0 + (875336457/2000000000 : ℝ)*x 1 + (218834143/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786882093/2000000000 : ℝ)^4719 ≤ (6076285261961/20000000000000 : ℝ)^3695 := by
    have hnat : (786882093 : ℕ)^4719*20000000000000^3695 ≤ 6076285261961^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786882093 2000000000 6076285261961 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (875336457/2000000000 : ℝ)^4719 ≤ (34809283920139/100000000000000 : ℝ)^3695 := by
    have hnat : (875336457 : ℕ)^4719*100000000000000^3695 ≤ 34809283920139^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875336457 2000000000 34809283920139 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218834143/500000000 : ℝ)^4719 ≤ (6961857952137/20000000000000 : ℝ)^3695 := by
    have hnat : (218834143 : ℕ)^4719*20000000000000^3695 ≤ 6961857952137^3695*500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218834143 500000000 6961857952137 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(786882093/2000000000 : ℝ), (875336457/2000000000 : ℝ), (218834143/500000000 : ℝ)] ![(6076285261961/20000000000000 : ℝ), (34809283920139/100000000000000 : ℝ), (6961857952137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(786882093/2000000000 : ℝ)|^4719 ≤ (6076285261961/20000000000000 : ℝ)^3695
        have hw : |(786882093/2000000000 : ℝ)|=(786882093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(875336457/2000000000 : ℝ)|^4719 ≤ (34809283920139/100000000000000 : ℝ)^3695
        have hw : |(875336457/2000000000 : ℝ)|=(875336457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218834143/500000000 : ℝ)|^4719 ≤ (6961857952137/20000000000000 : ℝ)^3695
        have hw : |(218834143/500000000 : ℝ)|=(218834143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_8 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897855579/10000000000 : ℝ)*x 0 + (1266438897/2500000000 : ℝ)*x 1 + (1362682651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897855579/10000000000 : ℝ)^4719 ≤ (11974222461429/100000000000000 : ℝ)^3695 := by
    have hnat : (1897855579 : ℕ)^4719*100000000000000^3695 ≤ 11974222461429^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897855579 10000000000 11974222461429 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266438897/2500000000 : ℝ)^4719 ≤ (20977895654667/50000000000000 : ℝ)^3695 := by
    have hnat : (1266438897 : ℕ)^4719*50000000000000^3695 ≤ 20977895654667^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266438897 2500000000 20977895654667 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362682651/2500000000 : ℝ)^4719 ≤ (46069986226871/100000000000000 : ℝ)^3695 := by
    have hnat : (1362682651 : ℕ)^4719*100000000000000^3695 ≤ 46069986226871^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362682651 2500000000 46069986226871 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897855579/10000000000 : ℝ), (1266438897/2500000000 : ℝ), (1362682651/2500000000 : ℝ)] ![(11974222461429/100000000000000 : ℝ), (20977895654667/50000000000000 : ℝ), (46069986226871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897855579/10000000000 : ℝ)|^4719 ≤ (11974222461429/100000000000000 : ℝ)^3695
        have hw : |(-1897855579/10000000000 : ℝ)|=(1897855579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266438897/2500000000 : ℝ)|^4719 ≤ (20977895654667/50000000000000 : ℝ)^3695
        have hw : |(1266438897/2500000000 : ℝ)|=(1266438897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362682651/2500000000 : ℝ)|^4719 ≤ (46069986226871/100000000000000 : ℝ)^3695
        have hw : |(1362682651/2500000000 : ℝ)|=(1362682651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_9 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046044051/2000000000 : ℝ)*x 0 + (-838672723/5000000000 : ℝ)*x 1 + (2725365201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046044051/2000000000 : ℝ)^4719 ≤ (21851591341391/50000000000000 : ℝ)^3695 := by
    have hnat : (1046044051 : ℕ)^4719*50000000000000^3695 ≤ 21851591341391^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046044051 2000000000 21851591341391 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (838672723/5000000000 : ℝ)^4719 ≤ (10226833265131/100000000000000 : ℝ)^3695 := by
    have hnat : (838672723 : ℕ)^4719*100000000000000^3695 ≤ 10226833265131^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838672723 5000000000 10226833265131 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725365201/5000000000 : ℝ)^4719 ≤ (28793740029/62500000000 : ℝ)^3695 := by
    have hnat : (2725365201 : ℕ)^4719*62500000000^3695 ≤ 28793740029^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725365201 5000000000 28793740029 62500000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046044051/2000000000 : ℝ), (-838672723/5000000000 : ℝ), (2725365201/5000000000 : ℝ)] ![(21851591341391/50000000000000 : ℝ), (10226833265131/100000000000000 : ℝ), (28793740029/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046044051/2000000000 : ℝ)|^4719 ≤ (21851591341391/50000000000000 : ℝ)^3695
        have hw : |(1046044051/2000000000 : ℝ)|=(1046044051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-838672723/5000000000 : ℝ)|^4719 ≤ (10226833265131/100000000000000 : ℝ)^3695
        have hw : |(-838672723/5000000000 : ℝ)|=(838672723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725365201/5000000000 : ℝ)|^4719 ≤ (28793740029/62500000000 : ℝ)^3695
        have hw : |(2725365201/5000000000 : ℝ)|=(2725365201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_10 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261511013/500000000 : ℝ)*x 0 + (1090146129/2000000000 : ℝ)*x 1 + (-838672551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261511013/500000000 : ℝ)^4719 ≤ (2185159136807/5000000000000 : ℝ)^3695 := by
    have hnat : (261511013 : ℕ)^4719*5000000000000^3695 ≤ 2185159136807^3695*500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261511013 500000000 2185159136807 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090146129/2000000000 : ℝ)^4719 ≤ (46069986669441/100000000000000 : ℝ)^3695 := by
    have hnat : (1090146129 : ℕ)^4719*100000000000000^3695 ≤ 46069986669441^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090146129 2000000000 46069986669441 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838672551/5000000000 : ℝ)^4719 ≤ (5113415293251/50000000000000 : ℝ)^3695 := by
    have hnat : (838672551 : ℕ)^4719*50000000000000^3695 ≤ 5113415293251^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838672551 5000000000 5113415293251 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261511013/500000000 : ℝ), (1090146129/2000000000 : ℝ), (-838672551/5000000000 : ℝ)] ![(2185159136807/5000000000000 : ℝ), (46069986669441/100000000000000 : ℝ), (5113415293251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261511013/500000000 : ℝ)|^4719 ≤ (2185159136807/5000000000000 : ℝ)^3695
        have hw : |(261511013/500000000 : ℝ)|=(261511013/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090146129/2000000000 : ℝ)|^4719 ≤ (46069986669441/100000000000000 : ℝ)^3695
        have hw : |(1090146129/2000000000 : ℝ)|=(1090146129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-838672551/5000000000 : ℝ)|^4719 ≤ (5113415293251/50000000000000 : ℝ)^3695
        have hw : |(-838672551/5000000000 : ℝ)|=(838672551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_11 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (572692029/1250000000 : ℝ)*x 0 + (4052244539/10000000000 : ℝ)*x 1 + (4052243397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572692029/1250000000 : ℝ)^4719 ≤ (18451714080421/50000000000000 : ℝ)^3695 := by
    have hnat : (572692029 : ℕ)^4719*50000000000000^3695 ≤ 18451714080421^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572692029 1250000000 18451714080421 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4052244539/10000000000 : ℝ)^4719 ≤ (31548291592199/100000000000000 : ℝ)^3695 := by
    have hnat : (4052244539 : ℕ)^4719*100000000000000^3695 ≤ 31548291592199^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052244539 10000000000 31548291592199 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052243397/10000000000 : ℝ)^4719 ≤ (15774140118669/50000000000000 : ℝ)^3695 := by
    have hnat : (4052243397 : ℕ)^4719*50000000000000^3695 ≤ 15774140118669^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052243397 10000000000 15774140118669 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(572692029/1250000000 : ℝ), (4052244539/10000000000 : ℝ), (4052243397/10000000000 : ℝ)] ![(18451714080421/50000000000000 : ℝ), (31548291592199/100000000000000 : ℝ), (15774140118669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(572692029/1250000000 : ℝ)|^4719 ≤ (18451714080421/50000000000000 : ℝ)^3695
        have hw : |(572692029/1250000000 : ℝ)|=(572692029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4052244539/10000000000 : ℝ)|^4719 ≤ (31548291592199/100000000000000 : ℝ)^3695
        have hw : |(4052244539/10000000000 : ℝ)|=(4052244539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4052243397/10000000000 : ℝ)|^4719 ≤ (15774140118669/50000000000000 : ℝ)^3695
        have hw : |(4052243397/10000000000 : ℝ)|=(4052243397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_12 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1571434051/10000000000 : ℝ)*x 0 + (5562291773/10000000000 : ℝ)*x 1 + (5193614231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1571434051/10000000000 : ℝ)^4719 ≤ (4704730025949/50000000000000 : ℝ)^3695 := by
    have hnat : (1571434051 : ℕ)^4719*50000000000000^3695 ≤ 4704730025949^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1571434051 10000000000 4704730025949 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5562291773/10000000000 : ℝ)^4719 ≤ (11819405443799/25000000000000 : ℝ)^3695 := by
    have hnat : (5562291773 : ℕ)^4719*25000000000000^3695 ≤ 11819405443799^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562291773 10000000000 11819405443799 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193614231/10000000000 : ℝ)^4719 ≤ (8662583630789/20000000000000 : ℝ)^3695 := by
    have hnat : (5193614231 : ℕ)^4719*20000000000000^3695 ≤ 8662583630789^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193614231 10000000000 8662583630789 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1571434051/10000000000 : ℝ), (5562291773/10000000000 : ℝ), (5193614231/10000000000 : ℝ)] ![(4704730025949/50000000000000 : ℝ), (11819405443799/25000000000000 : ℝ), (8662583630789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1571434051/10000000000 : ℝ)|^4719 ≤ (4704730025949/50000000000000 : ℝ)^3695
        have hw : |(-1571434051/10000000000 : ℝ)|=(1571434051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5562291773/10000000000 : ℝ)|^4719 ≤ (11819405443799/25000000000000 : ℝ)^3695
        have hw : |(5562291773/10000000000 : ℝ)|=(5562291773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193614231/10000000000 : ℝ)|^4719 ≤ (8662583630789/20000000000000 : ℝ)^3695
        have hw : |(5193614231/10000000000 : ℝ)|=(5193614231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_13 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407940247/10000000000 : ℝ)*x 0 + (-892881141/5000000000 : ℝ)*x 1 + (649201759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407940247/10000000000 : ℝ)^4719 ≤ (11402148245721/25000000000000 : ℝ)^3695 := by
    have hnat : (5407940247 : ℕ)^4719*25000000000000^3695 ≤ 11402148245721^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407940247 10000000000 11402148245721 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892881141/5000000000 : ℝ)^4719 ≤ (5539245269837/50000000000000 : ℝ)^3695 := by
    have hnat : (892881141 : ℕ)^4719*50000000000000^3695 ≤ 5539245269837^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892881141 5000000000 5539245269837 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649201759/1250000000 : ℝ)^4719 ≤ (43312916460463/100000000000000 : ℝ)^3695 := by
    have hnat : (649201759 : ℕ)^4719*100000000000000^3695 ≤ 43312916460463^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649201759 1250000000 43312916460463 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407940247/10000000000 : ℝ), (-892881141/5000000000 : ℝ), (649201759/1250000000 : ℝ)] ![(11402148245721/25000000000000 : ℝ), (5539245269837/50000000000000 : ℝ), (43312916460463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407940247/10000000000 : ℝ)|^4719 ≤ (11402148245721/25000000000000 : ℝ)^3695
        have hw : |(5407940247/10000000000 : ℝ)|=(5407940247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-892881141/5000000000 : ℝ)|^4719 ≤ (5539245269837/50000000000000 : ℝ)^3695
        have hw : |(-892881141/5000000000 : ℝ)|=(892881141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649201759/1250000000 : ℝ)|^4719 ≤ (43312916460463/100000000000000 : ℝ)^3695
        have hw : |(649201759/1250000000 : ℝ)|=(649201759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_14 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407939027/10000000000 : ℝ)*x 0 + (2596807493/5000000000 : ℝ)*x 1 + (-223220339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407939027/10000000000 : ℝ)^4719 ≤ (45608579842437/100000000000000 : ℝ)^3695 := by
    have hnat : (5407939027 : ℕ)^4719*100000000000000^3695 ≤ 45608579842437^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407939027 10000000000 45608579842437 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596807493/5000000000 : ℝ)^4719 ≤ (43312926195319/100000000000000 : ℝ)^3695 := by
    have hnat : (2596807493 : ℕ)^4719*100000000000000^3695 ≤ 43312926195319^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596807493 5000000000 43312926195319 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223220339/1250000000 : ℝ)^4719 ≤ (5539246973293/50000000000000 : ℝ)^3695 := by
    have hnat : (223220339 : ℕ)^4719*50000000000000^3695 ≤ 5539246973293^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223220339 1250000000 5539246973293 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407939027/10000000000 : ℝ), (2596807493/5000000000 : ℝ), (-223220339/1250000000 : ℝ)] ![(45608579842437/100000000000000 : ℝ), (43312926195319/100000000000000 : ℝ), (5539246973293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407939027/10000000000 : ℝ)|^4719 ≤ (45608579842437/100000000000000 : ℝ)^3695
        have hw : |(5407939027/10000000000 : ℝ)|=(5407939027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596807493/5000000000 : ℝ)|^4719 ≤ (43312926195319/100000000000000 : ℝ)^3695
        have hw : |(2596807493/5000000000 : ℝ)|=(2596807493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223220339/1250000000 : ℝ)|^4719 ≤ (5539246973293/50000000000000 : ℝ)^3695
        have hw : |(-223220339/1250000000 : ℝ)|=(223220339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_box_15 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (969597449/2500000000 : ℝ)*x 0 + (27523767/62500000 : ℝ)*x 1 + (4403799203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (969597449/2500000000 : ℝ)^4719 ≤ (372875568697/1250000000000 : ℝ)^3695 := by
    have hnat : (969597449 : ℕ)^4719*1250000000000^3695 ≤ 372875568697^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969597449 2500000000 372875568697 1250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27523767/62500000 : ℝ)^4719 ≤ (701699902781/2000000000000 : ℝ)^3695 := by
    have hnat : (27523767 : ℕ)^4719*2000000000000^3695 ≤ 701699902781^3695*62500000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27523767 62500000 701699902781 2000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4403799203/10000000000 : ℝ)^4719 ≤ (35084959354017/100000000000000 : ℝ)^3695 := by
    have hnat : (4403799203 : ℕ)^4719*100000000000000^3695 ≤ 35084959354017^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403799203 10000000000 35084959354017 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(969597449/2500000000 : ℝ), (27523767/62500000 : ℝ), (4403799203/10000000000 : ℝ)] ![(372875568697/1250000000000 : ℝ), (701699902781/2000000000000 : ℝ), (35084959354017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(969597449/2500000000 : ℝ)|^4719 ≤ (372875568697/1250000000000 : ℝ)^3695
        have hw : |(969597449/2500000000 : ℝ)|=(969597449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27523767/62500000 : ℝ)|^4719 ≤ (701699902781/2000000000000 : ℝ)^3695
        have hw : |(27523767/62500000 : ℝ)|=(27523767/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4403799203/10000000000 : ℝ)|^4719 ≤ (35084959354017/100000000000000 : ℝ)^3695
        have hw : |(4403799203/10000000000 : ℝ)|=(4403799203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(8111/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29043/50000 : ℝ) ∧ (80231/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87721/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (324/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (324/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (324/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (324/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (324/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (324/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (324/3125 : ℝ) ^ (4715/1024 : ℝ) ≤ (1468064946166769/50000000000000000000 : ℝ) := by
    have hpowers : (324/3125 : ℝ)^4715 ≤ (1468064946166769/50000000000000000000 : ℝ)^1024 := by
      have hnat : (324 : ℕ)^4715*50000000000000000000^1024 ≤ 1468064946166769^1024*3125^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        324 3125 1468064946166769 50000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (324/3125 : ℝ)) (X := (1468064946166769/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16357/100000 : ℝ) ^ (4715/1024 : ℝ) ≤ (23960982188115077/100000000000000000000 : ℝ) := by
    have hpowers : (16357/100000 : ℝ)^4715 ≤ (23960982188115077/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16357 : ℕ)^4715*100000000000000000000^1024 ≤ 23960982188115077^1024*100000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16357 100000 23960982188115077 100000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16357/100000 : ℝ)) (X := (23960982188115077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001468064946166769/25000000000000000000 : ℝ) ≤ (10000127530345987/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (25001468064946166769/25000000000000000000 : ℝ)^1024 ≤ (10000127530345987/10000000000000000 : ℝ)^4715 := by
      have hnat : (25001468064946166769 : ℕ)^1024*10000000000000000^4715 ≤ 10000127530345987^4715*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001468064946166769 25000000000000000000 10000127530345987 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000127530345987/10000000000000000 : ℝ)) (X := (25001468064946166769/25000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005379422416089723/20000000000000000000 : ℝ) ≤ (2000116817576233/2000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (20005379422416089723/20000000000000000000 : ℝ)^1024 ≤ (2000116817576233/2000000000000000 : ℝ)^4715 := by
      have hnat : (20005379422416089723 : ℕ)^1024*2000000000000000^4715 ≤ 2000116817576233^4715*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005379422416089723 20000000000000000000 2000116817576233 2000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000116817576233/2000000000000000 : ℝ)) (X := (20005379422416089723/20000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023960982188115077/50000000000000000000 : ℝ) ≤ (10001040645416343/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (50023960982188115077/50000000000000000000 : ℝ)^1024 ≤ (10001040645416343/10000000000000000 : ℝ)^4715 := by
      have hnat : (50023960982188115077 : ℕ)^1024*10000000000000000^4715 ≤ 10001040645416343^4715*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023960982188115077 50000000000000000000 10001040645416343 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001040645416343/10000000000000000 : ℝ)) (X := (50023960982188115077/50000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1468064946166769/50000000000000000000 : ℝ) ≤ ((11976259320438533027/11978000000000000000 : ℝ)+2*(228278767589/299450000000000 : ℝ)*(324/3125 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (11976259320438533027/11978000000000000000 : ℝ)+2*(228278767589/299450000000000 : ℝ)*(324/3125 : ℝ)=(10000127530345987/10000000000000000 : ℝ) by norm_num, show 1+2*(1468064946166769/50000000000000000000 : ℝ)=(25001468064946166769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23960982188115077/100000000000000000000 : ℝ)+(1468064946166769/50000000000000000000 : ℝ) ≤ ((11976259320438533027/11978000000000000000 : ℝ)+(228278767589/299450000000000 : ℝ)*((16357/100000 : ℝ)+(324/3125 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (11976259320438533027/11978000000000000000 : ℝ)+(228278767589/299450000000000 : ℝ)*((16357/100000 : ℝ)+(324/3125 : ℝ))=(2000116817576233/2000000000000000 : ℝ) by norm_num, show 1+(23960982188115077/100000000000000000000 : ℝ)+(1468064946166769/50000000000000000000 : ℝ)=(20005379422416089723/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23960982188115077/100000000000000000000 : ℝ) ≤ ((11976259320438533027/11978000000000000000 : ℝ)+2*(228278767589/299450000000000 : ℝ)*(16357/100000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (11976259320438533027/11978000000000000000 : ℝ)+2*(228278767589/299450000000000 : ℝ)*(16357/100000 : ℝ)=(10001040645416343/10000000000000000 : ℝ) by norm_num, show 1+2*(23960982188115077/100000000000000000000 : ℝ)=(50023960982188115077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11976259320438533027/11978000000000000000 : ℝ)*(X 1 0+X 2 0)+(228278767589/299450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (16357/100000 : ℝ)) (c := (11976259320438533027/11978000000000000000 : ℝ)) (alpha := (228278767589/299450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11976259320438533027/11978000000000000000 : ℝ)*(X 0 1+X 2 1)+(228278767589/299450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (16357/100000 : ℝ)) (c := (11976259320438533027/11978000000000000000 : ℝ)) (alpha := (228278767589/299450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11976259320438533027/11978000000000000000 : ℝ)*(X 0 2+X 1 2)+(228278767589/299450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (324/3125 : ℝ)) (hi := (16357/100000 : ℝ)) (c := (11976259320438533027/11978000000000000000 : ℝ)) (alpha := (228278767589/299450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-363089261/2500000000 : ℝ)*X 0 0+(1084133059/2000000000 : ℝ)*X 0 1+(5420666453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625502547/5000000000 : ℝ)*X 1 0+(-211309301/1250000000 : ℝ)*X 1 1+(1084133347/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251006623/10000000000 : ℝ)*X 2 0+(1355166427/2500000000 : ℝ)*X 2 1+(-845236867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4501627443/10000000000 : ℝ)*X 0 0+(4093421867/10000000000 : ℝ)*X 0 1+(51167799/125000000 : ℝ)*X 0 2+(4501627443/10000000000 : ℝ)*X 1 0+(4093421867/10000000000 : ℝ)*X 1 1+(51167799/125000000 : ℝ)*X 1 2+(4501627443/10000000000 : ℝ)*X 2 0+(4093421867/10000000000 : ℝ)*X 2 1+(51167799/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2017998423/10000000000 : ℝ)*X 0 0+(2606741819/5000000000 : ℝ)*X 0 1+(2606742093/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5394201267/10000000000 : ℝ)*X 1 0+(-222212827/1250000000 : ℝ)*X 1 1+(5213484227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2697101139/5000000000 : ℝ)*X 2 0+(1303370707/2500000000 : ℝ)*X 2 1+(-1777703127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((786882093/2000000000 : ℝ)*X 0 0+(875336457/2000000000 : ℝ)*X 0 1+(218834143/500000000 : ℝ)*X 0 2+(786882093/2000000000 : ℝ)*X 1 0+(875336457/2000000000 : ℝ)*X 1 1+(218834143/500000000 : ℝ)*X 1 2+(786882093/2000000000 : ℝ)*X 2 0+(875336457/2000000000 : ℝ)*X 2 1+(218834143/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1897855579/10000000000 : ℝ)*X 0 0+(1266438897/2500000000 : ℝ)*X 0 1+(1362682651/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046044051/2000000000 : ℝ)*X 1 0+(-838672723/5000000000 : ℝ)*X 1 1+(2725365201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((261511013/500000000 : ℝ)*X 2 0+(1090146129/2000000000 : ℝ)*X 2 1+(-838672551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((572692029/1250000000 : ℝ)*X 0 0+(4052244539/10000000000 : ℝ)*X 0 1+(4052243397/10000000000 : ℝ)*X 0 2+(572692029/1250000000 : ℝ)*X 1 0+(4052244539/10000000000 : ℝ)*X 1 1+(4052243397/10000000000 : ℝ)*X 1 2+(572692029/1250000000 : ℝ)*X 2 0+(4052244539/10000000000 : ℝ)*X 2 1+(4052243397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1571434051/10000000000 : ℝ)*X 0 0+(5562291773/10000000000 : ℝ)*X 0 1+(5193614231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5407940247/10000000000 : ℝ)*X 1 0+(-892881141/5000000000 : ℝ)*X 1 1+(649201759/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5407939027/10000000000 : ℝ)*X 2 0+(2596807493/5000000000 : ℝ)*X 2 1+(-223220339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((969597449/2500000000 : ℝ)*X 0 0+(27523767/62500000 : ℝ)*X 0 1+(4403799203/10000000000 : ℝ)*X 0 2+(969597449/2500000000 : ℝ)*X 1 0+(27523767/62500000 : ℝ)*X 1 1+(4403799203/10000000000 : ℝ)*X 1 2+(969597449/2500000000 : ℝ)*X 2 0+(27523767/62500000 : ℝ)*X 2 1+(4403799203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8111/12500 : ℝ) ≤ (-388601415387665952933037471978647/598900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1841547/10000000000000 : ℝ)*(upper1) + (7442669/25000000000000 : ℝ)*(lower4) + (5839087/5000000000000 : ℝ)*(upper5) + (1662071765929313/100000000000000 : ℝ)*(major0) + (1662071765929313/100000000000000 : ℝ)*(major1) + (1662071765929313/100000000000000 : ℝ)*(major2) + (867546061/5000000000000 : ℝ)*(sp2) + (3789524319/100000000000000 : ℝ)*(sp3) + (1187611125761501/50000000000000 : ℝ)*(sp4) + (7422525258143/312500000000 : ℝ)*(sp5) + (1187603171421169/50000000000000 : ℝ)*(sp6) + (970544668562267/100000000000000 : ℝ)*(sp7) + (288448111/20000000000000 : ℝ)*(sp12) + (7805578899/50000000000000 : ℝ)*(sp13) + (485274229043293/50000000000000 : ℝ)*(f.failure) + (1187611846881779/50000000000000 : ℝ)*(f.sum) + (5955634209631/29945000000000000000000000000 : ℝ)*base66 + (3134208905462000451/1197800000000000000000000000000000 : ℝ)*base67 + (2990449287241600451/1197800000000000000000000000000000 : ℝ)*base69 + (4734720873152199549/1197800000000000000000000000000000 : ℝ)*base72 + (14703293180663/14972500000000000000000000000 : ℝ)*base74 + (4686366379480599549/1197800000000000000000000000000000 : ℝ)*base76 + (5549335068356599549/1197800000000000000000000000000000 : ℝ)*base78 + (1737004533405399549/1197800000000000000000000000000000 : ℝ)*base80 + (11395323731029/7486250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1730671/625000000000000000000 : ℝ)*base89 + (1730671/625000000000000000000 : ℝ)*base91 + (1730671/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29043/50000 : ℝ) ≤ (8697280862792056716484245383367/14972500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3343417/4000000000000 : ℝ)*(lower1) + (345667937/100000000000000 : ℝ)*(lower3) + (165765489/100000000000000 : ℝ)*(upper4) + (36356937/50000000000000 : ℝ)*(upper5) + (87273133111693/5000000000000 : ℝ)*(major0) + (87273133111693/5000000000000 : ℝ)*(major1) + (87273133111693/5000000000000 : ℝ)*(major2) + (2452318883884249/100000000000000 : ℝ)*(sp0) + (613075724037349/25000000000000 : ℝ)*(sp1) + (2452317505059137/100000000000000 : ℝ)*(sp2) + (254810038267537/25000000000000 : ℝ)*(sp3) + (7993867427/50000000000000 : ℝ)*(sp5) + (172353139/12500000000000 : ℝ)*(sp6) + (218641259/6250000000000 : ℝ)*(sp7) + (254810912832573/25000000000000 : ℝ)*(f.failure) + (2452318883884249/100000000000000 : ℝ)*(f.sum) + (203214265651/93578125000000000000000000 : ℝ)*base65 + (182407015246674711/59890000000000000000000000000000 : ℝ)*base67 + (652552080355134711/59890000000000000000000000000000 : ℝ)*base69 + (20269935221724711/59890000000000000000000000000000 : ℝ)*base71 + (545310111919/299450000000000000000000000 : ℝ)*base73 + (2125463004881555289/59890000000000000000000000000000 : ℝ)*base76 + (186776937008674711/59890000000000000000000000000000 : ℝ)*base77 + (103129886977144711/59890000000000000000000000000000 : ℝ)*base79 + (8741961984407/2994500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1959169/312500000000000000000 : ℝ)*base90 + (1959169/312500000000000000000 : ℝ)*base92 + (1959169/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80231/100000 : ℝ) ≤ (240260426532040842486624934015503/299450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70898943/100000000000000 : ℝ)*(upper1) + (26772371/50000000000000 : ℝ)*(upper2) + (9459267/50000000000000 : ℝ)*(upper3) + (35716933/25000000000000 : ℝ)*(upper4) + (926626361463821/50000000000000 : ℝ)*(major0) + (926626361463821/50000000000000 : ℝ)*(major1) + (926626361463821/50000000000000 : ℝ)*(major2) + (40795541/25000000000000 : ℝ)*(sp0) + (4234709221/10000000000000 : ℝ)*(sp2) + (23786193219/100000000000000 : ℝ)*(sp3) + (2597574180647581/100000000000000 : ℝ)*(sp8) + (1298787171914873/50000000000000 : ℝ)*(sp9) + (634163085141/24414062500 : ℝ)*(sp10) + (27054067026347/2500000000000 : ℝ)*(sp11) + (1082186467247099/100000000000000 : ℝ)*(f.failure) + (1298787171914873/50000000000000 : ℝ)*(f.sum) + (42075169041907/14972500000000000000000000000 : ℝ)*base66 + (1648523675702023833/598900000000000000000000000000000 : ℝ)*base68 + (2225102585861523833/598900000000000000000000000000000 : ℝ)*base70 + (4164012798875423833/598900000000000000000000000000000 : ℝ)*base72 + (1395851726511/29945000000000000000000000000 : ℝ)*base73 + (8942439654317923833/598900000000000000000000000000000 : ℝ)*base76 + (5595791625819423833/598900000000000000000000000000000 : ℝ)*base78 + (5056680547070823833/598900000000000000000000000000000 : ℝ)*base80 + (21061852063523/3743125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (10937353/1250000000000000000000 : ℝ)*base89 + (10937353/1250000000000000000000 : ℝ)*base91 + (10937353/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-87721/100000 : ℝ) ≤ (-5253469178906611308845681264703/5989000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52532143/100000000000000 : ℝ)*(upper1) + (180284281/25000000000000 : ℝ)*(upper3) + (14771337/20000000000000 : ℝ)*(upper5) + (18948285340221/1000000000000 : ℝ)*(major0) + (18948285340221/1000000000000 : ℝ)*(major1) + (18948285340221/1000000000000 : ℝ)*(major2) + (5030479081/20000000000000 : ℝ)*(sp4) + (383343941243/100000000000000 : ℝ)*(sp5) + (142507313857/100000000000000 : ℝ)*(sp6) + (178159106743/100000000000000 : ℝ)*(sp7) + (54248145164711/2000000000000 : ℝ)*(sp12) + (169503066668107/6250000000000 : ℝ)*(sp13) + (1356144951658549/50000000000000 : ℝ)*(sp14) + (276571511005779/25000000000000 : ℝ)*(sp15) + (1106464203129859/100000000000000 : ℝ)*(f.failure) + (678108102657739/25000000000000 : ℝ)*(f.sum) + (1038328987057/2994500000000000000000000000 : ℝ)*base66 + (11645189756668967/11978000000000000000000000000000 : ℝ)*base67 + (366061727566714967/11978000000000000000000000000000 : ℝ)*base69 + (81902786453410967/11978000000000000000000000000000 : ℝ)*base71 + (41572665654407/5989000000000000000000000000 : ℝ)*base74 + (333967586355704967/11978000000000000000000000000000 : ℝ)*base75 + (84643878124644967/11978000000000000000000000000000 : ℝ)*base77 + (102393336371716967/11978000000000000000000000000000 : ℝ)*base79 + (32117594738803/5989000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2184927/1250000000000000000000 : ℝ)*base90 + (2184927/1250000000000000000000 : ℝ)*base92 + (2184927/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1600_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8111/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29043/50000 : ℝ) else (80231/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87721/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1600_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1600_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8111/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29043/50000 : ℝ) else (80231/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87721/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1600_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1600_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8111/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29043/50000 : ℝ) else (80231/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87721/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1600_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
