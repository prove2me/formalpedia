-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1613_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:51.248083+00:00
-- url     : https://prove2.me/submissions/04c42075-c86a-409f-b181-f0f47351a74d

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
theorem support_rectangle_w1613_box_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-712352253/5000000000 : ℝ)*x 0 + (1083466201/2000000000 : ℝ)*x 1 + (5417330883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (712352253/5000000000 : ℝ)^4771 ≤ (4182348652611/50000000000000 : ℝ)^3747 := by
    have hnat : (712352253 : ℕ)^4771*50000000000000^3747 ≤ 4182348652611^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712352253 5000000000 4182348652611 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083466201/2000000000 : ℝ)^4771 ≤ (45817651993241/100000000000000 : ℝ)^3747 := by
    have hnat : (1083466201 : ℕ)^4771*100000000000000^3747 ≤ 45817651993241^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083466201 2000000000 45817651993241 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417330883/10000000000 : ℝ)^4771 ≤ (45817650679429/100000000000000 : ℝ)^3747 := by
    have hnat : (5417330883 : ℕ)^4771*100000000000000^3747 ≤ 45817650679429^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417330883 10000000000 45817650679429 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-712352253/5000000000 : ℝ), (1083466201/2000000000 : ℝ), (5417330883/10000000000 : ℝ)] ![(4182348652611/50000000000000 : ℝ), (45817651993241/100000000000000 : ℝ), (45817650679429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-712352253/5000000000 : ℝ)|^4771 ≤ (4182348652611/50000000000000 : ℝ)^3747
        have hw : |(-712352253/5000000000 : ℝ)|=(712352253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083466201/2000000000 : ℝ)|^4771 ≤ (45817651993241/100000000000000 : ℝ)^3747
        have hw : |(1083466201/2000000000 : ℝ)|=(1083466201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417330883/10000000000 : ℝ)|^4771 ≤ (45817650679429/100000000000000 : ℝ)^3747
        have hw : |(5417330883/10000000000 : ℝ)|=(5417330883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050238223/2000000000 : ℝ)*x 0 + (-331599469/2000000000 : ℝ)*x 1 + (1354332669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050238223/2000000000 : ℝ)^4771 ≤ (44036054610487/100000000000000 : ℝ)^3747 := by
    have hnat : (1050238223 : ℕ)^4771*100000000000000^3747 ≤ 44036054610487^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050238223 2000000000 44036054610487 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331599469/2000000000 : ℝ)^4771 ≤ (10146296931733/100000000000000 : ℝ)^3747 := by
    have hnat : (331599469 : ℕ)^4771*100000000000000^3747 ≤ 10146296931733^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331599469 2000000000 10146296931733 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354332669/2500000000 : ℝ)^4771 ≤ (22908824225129/50000000000000 : ℝ)^3747 := by
    have hnat : (1354332669 : ℕ)^4771*50000000000000^3747 ≤ 22908824225129^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354332669 2500000000 22908824225129 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050238223/2000000000 : ℝ), (-331599469/2000000000 : ℝ), (1354332669/2500000000 : ℝ)] ![(44036054610487/100000000000000 : ℝ), (10146296931733/100000000000000 : ℝ), (22908824225129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050238223/2000000000 : ℝ)|^4771 ≤ (44036054610487/100000000000000 : ℝ)^3747
        have hw : |(1050238223/2000000000 : ℝ)|=(1050238223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331599469/2000000000 : ℝ)|^4771 ≤ (10146296931733/100000000000000 : ℝ)^3747
        have hw : |(-331599469/2000000000 : ℝ)|=(331599469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354332669/2500000000 : ℝ)|^4771 ≤ (22908824225129/50000000000000 : ℝ)^3747
        have hw : |(1354332669/2500000000 : ℝ)|=(1354332669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312797759/2500000000 : ℝ)*x 0 + (5417330863/10000000000 : ℝ)*x 1 + (-1657997193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312797759/2500000000 : ℝ)^4771 ≤ (44036053766951/100000000000000 : ℝ)^3747 := by
    have hnat : (1312797759 : ℕ)^4771*100000000000000^3747 ≤ 44036053766951^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312797759 2500000000 44036053766951 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417330863/10000000000 : ℝ)^4771 ≤ (45817650464051/100000000000000 : ℝ)^3747 := by
    have hnat : (5417330863 : ℕ)^4771*100000000000000^3747 ≤ 45817650464051^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417330863 10000000000 45817650464051 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1657997193/10000000000 : ℝ)^4771 ≤ (10146295747347/100000000000000 : ℝ)^3747 := by
    have hnat : (1657997193 : ℕ)^4771*100000000000000^3747 ≤ 10146295747347^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657997193 10000000000 10146295747347 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312797759/2500000000 : ℝ), (5417330863/10000000000 : ℝ), (-1657997193/10000000000 : ℝ)] ![(44036053766951/100000000000000 : ℝ), (45817650464051/100000000000000 : ℝ), (10146295747347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312797759/2500000000 : ℝ)|^4771 ≤ (44036053766951/100000000000000 : ℝ)^3747
        have hw : |(1312797759/2500000000 : ℝ)|=(1312797759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417330863/10000000000 : ℝ)|^4771 ≤ (45817650464051/100000000000000 : ℝ)^3747
        have hw : |(5417330863/10000000000 : ℝ)|=(5417330863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1657997193/10000000000 : ℝ)|^4771 ≤ (10146295747347/100000000000000 : ℝ)^3747
        have hw : |(-1657997193/10000000000 : ℝ)|=(1657997193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (179587321/400000000 : ℝ)*x 0 + (4082961043/10000000000 : ℝ)*x 1 + (1020740269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179587321/400000000 : ℝ)^4771 ≤ (721441857151/2000000000000 : ℝ)^3747 := by
    have hnat : (179587321 : ℕ)^4771*2000000000000^3747 ≤ 721441857151^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179587321 400000000 721441857151 2000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4082961043/10000000000 : ℝ)^4771 ≤ (15981976701411/50000000000000 : ℝ)^3747 := by
    have hnat : (4082961043 : ℕ)^4771*50000000000000^3747 ≤ 15981976701411^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082961043 10000000000 15981976701411 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020740269/2500000000 : ℝ)^4771 ≤ (3995494216471/12500000000000 : ℝ)^3747 := by
    have hnat : (1020740269 : ℕ)^4771*12500000000000^3747 ≤ 3995494216471^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020740269 2500000000 3995494216471 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179587321/400000000 : ℝ), (4082961043/10000000000 : ℝ), (1020740269/2500000000 : ℝ)] ![(721441857151/2000000000000 : ℝ), (15981976701411/50000000000000 : ℝ), (3995494216471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179587321/400000000 : ℝ)|^4771 ≤ (721441857151/2000000000000 : ℝ)^3747
        have hw : |(179587321/400000000 : ℝ)|=(179587321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4082961043/10000000000 : ℝ)|^4771 ≤ (15981976701411/50000000000000 : ℝ)^3747
        have hw : |(4082961043/10000000000 : ℝ)|=(4082961043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1020740269/2500000000 : ℝ)|^4771 ≤ (3995494216471/12500000000000 : ℝ)^3747
        have hw : |(1020740269/2500000000 : ℝ)|=(1020740269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1979571001/10000000000 : ℝ)*x 0 + (5214273279/10000000000 : ℝ)*x 1 + (5214273227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1979571001/10000000000 : ℝ)^4771 ≤ (3178881309161/25000000000000 : ℝ)^3747 := by
    have hnat : (1979571001 : ℕ)^4771*25000000000000^3747 ≤ 3178881309161^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979571001 10000000000 3178881309161 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214273279/10000000000 : ℝ)^4771 ≤ (43642237647789/100000000000000 : ℝ)^3747 := by
    have hnat : (5214273279 : ℕ)^4771*100000000000000^3747 ≤ 43642237647789^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214273279 10000000000 43642237647789 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214273227/10000000000 : ℝ)^4771 ≤ (2182111854681/5000000000000 : ℝ)^3747 := by
    have hnat : (5214273227 : ℕ)^4771*5000000000000^3747 ≤ 2182111854681^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214273227 10000000000 2182111854681 5000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1979571001/10000000000 : ℝ), (5214273279/10000000000 : ℝ), (5214273227/10000000000 : ℝ)] ![(3178881309161/25000000000000 : ℝ), (43642237647789/100000000000000 : ℝ), (2182111854681/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1979571001/10000000000 : ℝ)|^4771 ≤ (3178881309161/25000000000000 : ℝ)^3747
        have hw : |(-1979571001/10000000000 : ℝ)|=(1979571001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214273279/10000000000 : ℝ)|^4771 ≤ (43642237647789/100000000000000 : ℝ)^3747
        have hw : |(5214273279/10000000000 : ℝ)|=(5214273279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214273227/10000000000 : ℝ)|^4771 ≤ (2182111854681/5000000000000 : ℝ)^3747
        have hw : |(5214273227/10000000000 : ℝ)|=(5214273227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391277083/10000000000 : ℝ)*x 0 + (-348784289/2000000000 : ℝ)*x 1 + (325892067/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391277083/10000000000 : ℝ)^4771 ≤ (9107452664859/20000000000000 : ℝ)^3747 := by
    have hnat : (5391277083 : ℕ)^4771*20000000000000^3747 ≤ 9107452664859^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391277083 10000000000 9107452664859 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348784289/2000000000 : ℝ)^4771 ≤ (2164100244327/20000000000000 : ℝ)^3747 := by
    have hnat : (348784289 : ℕ)^4771*20000000000000^3747 ≤ 2164100244327^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348784289 2000000000 2164100244327 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325892067/625000000 : ℝ)^4771 ≤ (4364223544177/10000000000000 : ℝ)^3747 := by
    have hnat : (325892067 : ℕ)^4771*10000000000000^3747 ≤ 4364223544177^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325892067 625000000 4364223544177 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391277083/10000000000 : ℝ), (-348784289/2000000000 : ℝ), (325892067/625000000 : ℝ)] ![(9107452664859/20000000000000 : ℝ), (2164100244327/20000000000000 : ℝ), (4364223544177/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391277083/10000000000 : ℝ)|^4771 ≤ (9107452664859/20000000000000 : ℝ)^3747
        have hw : |(5391277083/10000000000 : ℝ)|=(5391277083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-348784289/2000000000 : ℝ)|^4771 ≤ (2164100244327/20000000000000 : ℝ)^3747
        have hw : |(-348784289/2000000000 : ℝ)|=(348784289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325892067/625000000 : ℝ)|^4771 ≤ (4364223544177/10000000000000 : ℝ)^3747
        have hw : |(325892067/625000000 : ℝ)|=(325892067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391276687/10000000000 : ℝ)*x 0 + (5214273269/10000000000 : ℝ)*x 1 + (-1743921717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391276687/10000000000 : ℝ)^4771 ≤ (711519672897/1562500000000 : ℝ)^3747 := by
    have hnat : (5391276687 : ℕ)^4771*1562500000000^3747 ≤ 711519672897^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391276687 10000000000 711519672897 1562500000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214273269/10000000000 : ℝ)^4771 ≤ (21821118770609/50000000000000 : ℝ)^3747 := by
    have hnat : (5214273269 : ℕ)^4771*50000000000000^3747 ≤ 21821118770609^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214273269 10000000000 21821118770609 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1743921717/10000000000 : ℝ)^4771 ≤ (10820503370529/100000000000000 : ℝ)^3747 := by
    have hnat : (1743921717 : ℕ)^4771*100000000000000^3747 ≤ 10820503370529^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743921717 10000000000 10820503370529 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391276687/10000000000 : ℝ), (5214273269/10000000000 : ℝ), (-1743921717/10000000000 : ℝ)] ![(711519672897/1562500000000 : ℝ), (21821118770609/50000000000000 : ℝ), (10820503370529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391276687/10000000000 : ℝ)|^4771 ≤ (711519672897/1562500000000 : ℝ)^3747
        have hw : |(5391276687/10000000000 : ℝ)|=(5391276687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214273269/10000000000 : ℝ)|^4771 ≤ (21821118770609/50000000000000 : ℝ)^3747
        have hw : |(5214273269/10000000000 : ℝ)|=(5214273269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1743921717/10000000000 : ℝ)|^4771 ≤ (10820503370529/100000000000000 : ℝ)^3747
        have hw : |(-1743921717/10000000000 : ℝ)|=(1743921717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (784913081/2000000000 : ℝ)*x 0 + (2182589057/5000000000 : ℝ)*x 1 + (2182588829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784913081/2000000000 : ℝ)^4771 ≤ (30393504641393/100000000000000 : ℝ)^3747 := by
    have hnat : (784913081 : ℕ)^4771*100000000000000^3747 ≤ 30393504641393^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784913081 2000000000 30393504641393 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182589057/5000000000 : ℝ)^4771 ≤ (34803249990113/100000000000000 : ℝ)^3747 := by
    have hnat : (2182589057 : ℕ)^4771*100000000000000^3747 ≤ 34803249990113^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182589057 5000000000 34803249990113 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182588829/5000000000 : ℝ)^4771 ≤ (34803245360887/100000000000000 : ℝ)^3747 := by
    have hnat : (2182588829 : ℕ)^4771*100000000000000^3747 ≤ 34803245360887^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182588829 5000000000 34803245360887 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(784913081/2000000000 : ℝ), (2182589057/5000000000 : ℝ), (2182588829/5000000000 : ℝ)] ![(30393504641393/100000000000000 : ℝ), (34803249990113/100000000000000 : ℝ), (34803245360887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(784913081/2000000000 : ℝ)|^4771 ≤ (30393504641393/100000000000000 : ℝ)^3747
        have hw : |(784913081/2000000000 : ℝ)|=(784913081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2182589057/5000000000 : ℝ)|^4771 ≤ (34803249990113/100000000000000 : ℝ)^3747
        have hw : |(2182589057/5000000000 : ℝ)|=(2182589057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2182588829/5000000000 : ℝ)|^4771 ≤ (34803245360887/100000000000000 : ℝ)^3747
        have hw : |(2182588829/5000000000 : ℝ)|=(2182588829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_8 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-930784059/5000000000 : ℝ)*x 0 + (1267289141/2500000000 : ℝ)*x 1 + (1361809967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930784059/5000000000 : ℝ)^4771 ≤ (5879191216043/50000000000000 : ℝ)^3747 := by
    have hnat : (930784059 : ℕ)^4771*50000000000000^3747 ≤ 5879191216043^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930784059 5000000000 5879191216043 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267289141/2500000000 : ℝ)^4771 ≤ (4210163598497/10000000000000 : ℝ)^3747 := by
    have hnat : (1267289141 : ℕ)^4771*10000000000000^3747 ≤ 4210163598497^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267289141 2500000000 4210163598497 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361809967/2500000000 : ℝ)^4771 ≤ (23069990783773/50000000000000 : ℝ)^3747 := by
    have hnat : (1361809967 : ℕ)^4771*50000000000000^3747 ≤ 23069990783773^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361809967 2500000000 23069990783773 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930784059/5000000000 : ℝ), (1267289141/2500000000 : ℝ), (1361809967/2500000000 : ℝ)] ![(5879191216043/50000000000000 : ℝ), (4210163598497/10000000000000 : ℝ), (23069990783773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930784059/5000000000 : ℝ)|^4771 ≤ (5879191216043/50000000000000 : ℝ)^3747
        have hw : |(-930784059/5000000000 : ℝ)|=(930784059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267289141/2500000000 : ℝ)|^4771 ≤ (4210163598497/10000000000000 : ℝ)^3747
        have hw : |(1267289141/2500000000 : ℝ)|=(1267289141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361809967/2500000000 : ℝ)|^4771 ≤ (23069990783773/50000000000000 : ℝ)^3747
        have hw : |(1361809967/2500000000 : ℝ)|=(1361809967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_9 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523055307/1000000000 : ℝ)*x 0 + (-1644881539/10000000000 : ℝ)*x 1 + (2723620043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523055307/1000000000 : ℝ)^4771 ≤ (43815806930651/100000000000000 : ℝ)^3747 := by
    have hnat : (523055307 : ℕ)^4771*100000000000000^3747 ≤ 43815806930651^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523055307 1000000000 43815806930651 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1644881539/10000000000 : ℝ)^4771 ≤ (5022104565793/50000000000000 : ℝ)^3747 := by
    have hnat : (1644881539 : ℕ)^4771*50000000000000^3747 ≤ 5022104565793^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644881539 10000000000 5022104565793 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723620043/5000000000 : ℝ)^4771 ≤ (46139983918711/100000000000000 : ℝ)^3747 := by
    have hnat : (2723620043 : ℕ)^4771*100000000000000^3747 ≤ 46139983918711^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723620043 5000000000 46139983918711 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523055307/1000000000 : ℝ), (-1644881539/10000000000 : ℝ), (2723620043/5000000000 : ℝ)] ![(43815806930651/100000000000000 : ℝ), (5022104565793/50000000000000 : ℝ), (46139983918711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523055307/1000000000 : ℝ)|^4771 ≤ (43815806930651/100000000000000 : ℝ)^3747
        have hw : |(523055307/1000000000 : ℝ)|=(523055307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1644881539/10000000000 : ℝ)|^4771 ≤ (5022104565793/50000000000000 : ℝ)^3747
        have hw : |(-1644881539/10000000000 : ℝ)|=(1644881539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723620043/5000000000 : ℝ)|^4771 ≤ (46139983918711/100000000000000 : ℝ)^3747
        have hw : |(2723620043/5000000000 : ℝ)|=(2723620043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_10 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20431849/39062500 : ℝ)*x 0 + (5447240149/10000000000 : ℝ)*x 1 + (-65795243/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20431849/39062500 : ℝ)^4771 ≤ (8763161970637/20000000000000 : ℝ)^3747 := by
    have hnat : (20431849 : ℕ)^4771*20000000000000^3747 ≤ 8763161970637^3747*39062500^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20431849 39062500 8763161970637 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447240149/10000000000 : ℝ)^4771 ≤ (1441874518693/3125000000000 : ℝ)^3747 := by
    have hnat : (5447240149 : ℕ)^4771*3125000000000^3747 ≤ 1441874518693^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447240149 10000000000 1441874518693 3125000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65795243/400000000 : ℝ)^4771 ≤ (10044205523933/100000000000000 : ℝ)^3747 := by
    have hnat : (65795243 : ℕ)^4771*100000000000000^3747 ≤ 10044205523933^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65795243 400000000 10044205523933 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20431849/39062500 : ℝ), (5447240149/10000000000 : ℝ), (-65795243/400000000 : ℝ)] ![(8763161970637/20000000000000 : ℝ), (1441874518693/3125000000000 : ℝ), (10044205523933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20431849/39062500 : ℝ)|^4771 ≤ (8763161970637/20000000000000 : ℝ)^3747
        have hw : |(20431849/39062500 : ℝ)|=(20431849/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447240149/10000000000 : ℝ)|^4771 ≤ (1441874518693/3125000000000 : ℝ)^3747
        have hw : |(5447240149/10000000000 : ℝ)|=(5447240149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65795243/400000000 : ℝ)|^4771 ≤ (10044205523933/100000000000000 : ℝ)^3747
        have hw : |(-65795243/400000000 : ℝ)|=(65795243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_11 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4570526187/10000000000 : ℝ)*x 0 + (2020658619/5000000000 : ℝ)*x 1 + (4041316671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4570526187/10000000000 : ℝ)^4771 ≤ (295209243399/800000000000 : ℝ)^3747 := by
    have hnat : (4570526187 : ℕ)^4771*800000000000^3747 ≤ 295209243399^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570526187 10000000000 295209243399 800000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020658619/5000000000 : ℝ)^4771 ≤ (31549425099529/100000000000000 : ℝ)^3747 := by
    have hnat : (2020658619 : ℕ)^4771*100000000000000^3747 ≤ 31549425099529^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020658619 5000000000 31549425099529 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041316671/10000000000 : ℝ)^4771 ≤ (31549419463447/100000000000000 : ℝ)^3747 := by
    have hnat : (4041316671 : ℕ)^4771*100000000000000^3747 ≤ 31549419463447^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041316671 10000000000 31549419463447 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4570526187/10000000000 : ℝ), (2020658619/5000000000 : ℝ), (4041316671/10000000000 : ℝ)] ![(295209243399/800000000000 : ℝ), (31549425099529/100000000000000 : ℝ), (31549419463447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4570526187/10000000000 : ℝ)|^4771 ≤ (295209243399/800000000000 : ℝ)^3747
        have hw : |(4570526187/10000000000 : ℝ)|=(4570526187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2020658619/5000000000 : ℝ)|^4771 ≤ (31549425099529/100000000000000 : ℝ)^3747
        have hw : |(2020658619/5000000000 : ℝ)|=(2020658619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041316671/10000000000 : ℝ)|^4771 ≤ (31549419463447/100000000000000 : ℝ)^3747
        have hw : |(4041316671/10000000000 : ℝ)|=(4041316671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_12 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-770720389/5000000000 : ℝ)*x 0 + (5556578193/10000000000 : ℝ)*x 1 + (5194404427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (770720389/5000000000 : ℝ)^4771 ≤ (9246964532661/100000000000000 : ℝ)^3747 := by
    have hnat : (770720389 : ℕ)^4771*100000000000000^3747 ≤ 9246964532661^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770720389 5000000000 9246964532661 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5556578193/10000000000 : ℝ)^4771 ≤ (2957651983941/6250000000000 : ℝ)^3747 := by
    have hnat : (5556578193 : ℕ)^4771*6250000000000^3747 ≤ 2957651983941^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5556578193 10000000000 2957651983941 6250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194404427/10000000000 : ℝ)^4771 ≤ (10857650925909/25000000000000 : ℝ)^3747 := by
    have hnat : (5194404427 : ℕ)^4771*25000000000000^3747 ≤ 10857650925909^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194404427 10000000000 10857650925909 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-770720389/5000000000 : ℝ), (5556578193/10000000000 : ℝ), (5194404427/10000000000 : ℝ)] ![(9246964532661/100000000000000 : ℝ), (2957651983941/6250000000000 : ℝ), (10857650925909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-770720389/5000000000 : ℝ)|^4771 ≤ (9246964532661/100000000000000 : ℝ)^3747
        have hw : |(-770720389/5000000000 : ℝ)|=(770720389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5556578193/10000000000 : ℝ)|^4771 ≤ (2957651983941/6250000000000 : ℝ)^3747
        have hw : |(5556578193/10000000000 : ℝ)|=(5556578193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194404427/10000000000 : ℝ)|^4771 ≤ (10857650925909/25000000000000 : ℝ)^3747
        have hw : |(5194404427/10000000000 : ℝ)|=(5194404427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_13 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080998403/2000000000 : ℝ)*x 0 + (-876014779/5000000000 : ℝ)*x 1 + (259720137/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080998403/2000000000 : ℝ)^4771 ≤ (22842407730167/50000000000000 : ℝ)^3747 := by
    have hnat : (1080998403 : ℕ)^4771*50000000000000^3747 ≤ 22842407730167^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080998403 2000000000 22842407730167 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876014779/5000000000 : ℝ)^4771 ≤ (10884598779967/100000000000000 : ℝ)^3747 := by
    have hnat : (876014779 : ℕ)^4771*100000000000000^3747 ≤ 10884598779967^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876014779 5000000000 10884598779967 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259720137/500000000 : ℝ)^4771 ≤ (43430585743861/100000000000000 : ℝ)^3747 := by
    have hnat : (259720137 : ℕ)^4771*100000000000000^3747 ≤ 43430585743861^3747*500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259720137 500000000 43430585743861 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080998403/2000000000 : ℝ), (-876014779/5000000000 : ℝ), (259720137/500000000 : ℝ)] ![(22842407730167/50000000000000 : ℝ), (10884598779967/100000000000000 : ℝ), (43430585743861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080998403/2000000000 : ℝ)|^4771 ≤ (22842407730167/50000000000000 : ℝ)^3747
        have hw : |(1080998403/2000000000 : ℝ)|=(1080998403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-876014779/5000000000 : ℝ)|^4771 ≤ (10884598779967/100000000000000 : ℝ)^3747
        have hw : |(-876014779/5000000000 : ℝ)|=(876014779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259720137/500000000 : ℝ)|^4771 ≤ (43430585743861/100000000000000 : ℝ)^3747
        have hw : |(259720137/500000000 : ℝ)|=(259720137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_14 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404993651/10000000000 : ℝ)*x 0 + (5194401921/10000000000 : ℝ)*x 1 + (-876014217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404993651/10000000000 : ℝ)^4771 ≤ (9136966613471/20000000000000 : ℝ)^3747 := by
    have hnat : (5404993651 : ℕ)^4771*20000000000000^3747 ≤ 9136966613471^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404993651 10000000000 9136966613471 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194401921/10000000000 : ℝ)^4771 ≤ (54288221281/125000000000 : ℝ)^3747 := by
    have hnat : (5194401921 : ℕ)^4771*125000000000^3747 ≤ 54288221281^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194401921 10000000000 54288221281 125000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876014217/5000000000 : ℝ)^4771 ≤ (10884589888713/100000000000000 : ℝ)^3747 := by
    have hnat : (876014217 : ℕ)^4771*100000000000000^3747 ≤ 10884589888713^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876014217 5000000000 10884589888713 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404993651/10000000000 : ℝ), (5194401921/10000000000 : ℝ), (-876014217/5000000000 : ℝ)] ![(9136966613471/20000000000000 : ℝ), (54288221281/125000000000 : ℝ), (10884589888713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404993651/10000000000 : ℝ)|^4771 ≤ (9136966613471/20000000000000 : ℝ)^3747
        have hw : |(5404993651/10000000000 : ℝ)|=(5404993651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194401921/10000000000 : ℝ)|^4771 ≤ (54288221281/125000000000 : ℝ)^3747
        have hw : |(5194401921/10000000000 : ℝ)|=(5194401921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876014217/5000000000 : ℝ)|^4771 ≤ (10884589888713/100000000000000 : ℝ)^3747
        have hw : |(-876014217/5000000000 : ℝ)|=(876014217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_box_15 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3867644393/10000000000 : ℝ)*x 0 + (4392743081/10000000000 : ℝ)*x 1 + (68636639/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3867644393/10000000000 : ℝ)^4771 ≤ (5966666129377/20000000000000 : ℝ)^3747 := by
    have hnat : (3867644393 : ℕ)^4771*20000000000000^3747 ≤ 5966666129377^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867644393 10000000000 5966666129377 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392743081/10000000000 : ℝ)^4771 ≤ (17541662718027/50000000000000 : ℝ)^3747 := by
    have hnat : (4392743081 : ℕ)^4771*50000000000000^3747 ≤ 17541662718027^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392743081 10000000000 17541662718027 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68636639/156250000 : ℝ)^4771 ≤ (17541671946659/50000000000000 : ℝ)^3747 := by
    have hnat : (68636639 : ℕ)^4771*50000000000000^3747 ≤ 17541671946659^3747*156250000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68636639 156250000 17541671946659 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3867644393/10000000000 : ℝ), (4392743081/10000000000 : ℝ), (68636639/156250000 : ℝ)] ![(5966666129377/20000000000000 : ℝ), (17541662718027/50000000000000 : ℝ), (17541671946659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3867644393/10000000000 : ℝ)|^4771 ≤ (5966666129377/20000000000000 : ℝ)^3747
        have hw : |(3867644393/10000000000 : ℝ)|=(3867644393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4392743081/10000000000 : ℝ)|^4771 ≤ (17541662718027/50000000000000 : ℝ)^3747
        have hw : |(4392743081/10000000000 : ℝ)|=(4392743081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68636639/156250000 : ℝ)|^4771 ≤ (17541671946659/50000000000000 : ℝ)^3747
        have hw : |(68636639/156250000 : ℝ)|=(68636639/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64929/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29113/50000 : ℝ) ∧ (80493/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17571/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2091/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2091/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2091/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2091/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2091/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2091/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2091/20000 : ℝ) ^ (4767/1024 : ℝ) ≤ (2720728709443489/100000000000000000000 : ℝ) := by
    have hpowers : (2091/20000 : ℝ)^4767 ≤ (2720728709443489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2091 : ℕ)^4767*100000000000000000000^1024 ≤ 2720728709443489^1024*20000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2091 20000 2720728709443489 100000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2091/20000 : ℝ)) (X := (2720728709443489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1021/6250 : ℝ) ^ (4767/1024 : ℝ) ≤ (5431480214909343/25000000000000000000 : ℝ) := by
    have hpowers : (1021/6250 : ℝ)^4767 ≤ (5431480214909343/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1021 : ℕ)^4767*25000000000000000000^1024 ≤ 5431480214909343^1024*6250^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1021 6250 5431480214909343 25000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1021/6250 : ℝ)) (X := (5431480214909343/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002720728709443489/50000000000000000000 : ℝ) ≤ (10000116885533159/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50002720728709443489/50000000000000000000 : ℝ)^1024 ≤ (10000116885533159/10000000000000000 : ℝ)^4767 := by
      have hnat : (50002720728709443489 : ℕ)^1024*10000000000000000^4767 ≤ 10000116885533159^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002720728709443489 50000000000000000000 10000116885533159 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000116885533159/10000000000000000 : ℝ)) (X := (50002720728709443489/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024446649569080861/100000000000000000000 : ℝ) ≤ (2500131272115051/2500000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (100024446649569080861/100000000000000000000 : ℝ)^1024 ≤ (2500131272115051/2500000000000000 : ℝ)^4767 := by
      have hnat : (100024446649569080861 : ℕ)^1024*2500000000000000^4767 ≤ 2500131272115051^4767*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024446649569080861 100000000000000000000 2500131272115051 2500000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500131272115051/2500000000000000 : ℝ)) (X := (100024446649569080861/100000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505431480214909343/12500000000000000000 : ℝ) ≤ (10000933291387249/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (12505431480214909343/12500000000000000000 : ℝ)^1024 ≤ (10000933291387249/10000000000000000 : ℝ)^4767 := by
      have hnat : (12505431480214909343 : ℕ)^1024*10000000000000000^4767 ≤ 10000933291387249^4767*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505431480214909343 12500000000000000000 10000933291387249 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000933291387249/10000000000000000 : ℝ)) (X := (12505431480214909343/12500000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2720728709443489/100000000000000000000 : ℝ) ≤ ((58802151880615997129/58810000000000000000 : ℝ)+2*(81640585409/117620000000000 : ℝ)*(2091/20000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (58802151880615997129/58810000000000000000 : ℝ)+2*(81640585409/117620000000000 : ℝ)*(2091/20000 : ℝ)=(10000116885533159/10000000000000000 : ℝ) by norm_num, show 1+2*(2720728709443489/100000000000000000000 : ℝ)=(50002720728709443489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5431480214909343/25000000000000000000 : ℝ)+(2720728709443489/100000000000000000000 : ℝ) ≤ ((58802151880615997129/58810000000000000000 : ℝ)+(81640585409/117620000000000 : ℝ)*((1021/6250 : ℝ)+(2091/20000 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (58802151880615997129/58810000000000000000 : ℝ)+(81640585409/117620000000000 : ℝ)*((1021/6250 : ℝ)+(2091/20000 : ℝ))=(2500131272115051/2500000000000000 : ℝ) by norm_num, show 1+(5431480214909343/25000000000000000000 : ℝ)+(2720728709443489/100000000000000000000 : ℝ)=(100024446649569080861/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5431480214909343/25000000000000000000 : ℝ) ≤ ((58802151880615997129/58810000000000000000 : ℝ)+2*(81640585409/117620000000000 : ℝ)*(1021/6250 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (58802151880615997129/58810000000000000000 : ℝ)+2*(81640585409/117620000000000 : ℝ)*(1021/6250 : ℝ)=(10000933291387249/10000000000000000 : ℝ) by norm_num, show 1+2*(5431480214909343/25000000000000000000 : ℝ)=(12505431480214909343/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58802151880615997129/58810000000000000000 : ℝ)*(X 1 0+X 2 0)+(81640585409/117620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (2091/20000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (58802151880615997129/58810000000000000000 : ℝ)) (alpha := (81640585409/117620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58802151880615997129/58810000000000000000 : ℝ)*(X 0 1+X 2 1)+(81640585409/117620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (2091/20000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (58802151880615997129/58810000000000000000 : ℝ)) (alpha := (81640585409/117620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58802151880615997129/58810000000000000000 : ℝ)*(X 0 2+X 1 2)+(81640585409/117620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (2091/20000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (58802151880615997129/58810000000000000000 : ℝ)) (alpha := (81640585409/117620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-712352253/5000000000 : ℝ)*X 0 0+(1083466201/2000000000 : ℝ)*X 0 1+(5417330883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1050238223/2000000000 : ℝ)*X 1 0+(-331599469/2000000000 : ℝ)*X 1 1+(1354332669/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1312797759/2500000000 : ℝ)*X 2 0+(5417330863/10000000000 : ℝ)*X 2 1+(-1657997193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((179587321/400000000 : ℝ)*X 0 0+(4082961043/10000000000 : ℝ)*X 0 1+(1020740269/2500000000 : ℝ)*X 0 2+(179587321/400000000 : ℝ)*X 1 0+(4082961043/10000000000 : ℝ)*X 1 1+(1020740269/2500000000 : ℝ)*X 1 2+(179587321/400000000 : ℝ)*X 2 0+(4082961043/10000000000 : ℝ)*X 2 1+(1020740269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1979571001/10000000000 : ℝ)*X 0 0+(5214273279/10000000000 : ℝ)*X 0 1+(5214273227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5391277083/10000000000 : ℝ)*X 1 0+(-348784289/2000000000 : ℝ)*X 1 1+(325892067/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5391276687/10000000000 : ℝ)*X 2 0+(5214273269/10000000000 : ℝ)*X 2 1+(-1743921717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((784913081/2000000000 : ℝ)*X 0 0+(2182589057/5000000000 : ℝ)*X 0 1+(2182588829/5000000000 : ℝ)*X 0 2+(784913081/2000000000 : ℝ)*X 1 0+(2182589057/5000000000 : ℝ)*X 1 1+(2182588829/5000000000 : ℝ)*X 1 2+(784913081/2000000000 : ℝ)*X 2 0+(2182589057/5000000000 : ℝ)*X 2 1+(2182588829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-930784059/5000000000 : ℝ)*X 0 0+(1267289141/2500000000 : ℝ)*X 0 1+(1361809967/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((523055307/1000000000 : ℝ)*X 1 0+(-1644881539/10000000000 : ℝ)*X 1 1+(2723620043/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((20431849/39062500 : ℝ)*X 2 0+(5447240149/10000000000 : ℝ)*X 2 1+(-65795243/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4570526187/10000000000 : ℝ)*X 0 0+(2020658619/5000000000 : ℝ)*X 0 1+(4041316671/10000000000 : ℝ)*X 0 2+(4570526187/10000000000 : ℝ)*X 1 0+(2020658619/5000000000 : ℝ)*X 1 1+(4041316671/10000000000 : ℝ)*X 1 2+(4570526187/10000000000 : ℝ)*X 2 0+(2020658619/5000000000 : ℝ)*X 2 1+(4041316671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-770720389/5000000000 : ℝ)*X 0 0+(5556578193/10000000000 : ℝ)*X 0 1+(5194404427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1080998403/2000000000 : ℝ)*X 1 0+(-876014779/5000000000 : ℝ)*X 1 1+(259720137/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5404993651/10000000000 : ℝ)*X 2 0+(5194401921/10000000000 : ℝ)*X 2 1+(-876014217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3867644393/10000000000 : ℝ)*X 0 0+(4392743081/10000000000 : ℝ)*X 0 1+(68636639/156250000 : ℝ)*X 0 2+(3867644393/10000000000 : ℝ)*X 1 0+(4392743081/10000000000 : ℝ)*X 1 1+(68636639/156250000 : ℝ)*X 1 2+(3867644393/10000000000 : ℝ)*X 2 0+(4392743081/10000000000 : ℝ)*X 2 1+(68636639/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64929/100000 : ℝ) ≤ (-29830619423370590561694524511393/45945312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7409243/100000000000000 : ℝ)*(lower0) + (2521041/4000000000000 : ℝ)*(upper1) + (90631297/100000000000000 : ℝ)*(lower4) + (21510073/50000000000000 : ℝ)*(lower5) + (52737654634499/3125000000000 : ℝ)*(major0) + (52737654634499/3125000000000 : ℝ)*(major1) + (52737654634499/3125000000000 : ℝ)*(major2) + (167697159/20000000000000 : ℝ)*(sp3) + (2423341706106249/100000000000000 : ℝ)*(sp4) + (121166444545311/5000000000000 : ℝ)*(sp5) + (121166250244647/5000000000000 : ℝ)*(sp6) + (194701894465061/20000000000000 : ℝ)*(sp7) + (12815200029/100000000000000 : ℝ)*(sp13) + (1670121331/10000000000000 : ℝ)*(sp14) + (9735103108111/1000000000000 : ℝ)*(f.failure) + (2423341706106249/100000000000000 : ℝ)*(f.sum) + (3756879956881/5881000000000000000000000000 : ℝ)*base65 + (3145899213285709129/183781250000000000000000000000000 : ℝ)*base68 + (63642708422177879/183781250000000000000000000000000 : ℝ)*base70 + (102067960860365379/183781250000000000000000000000000 : ℝ)*base72 + (107141111884201/5881000000000000000000000000 : ℝ)*base74 + (1227141912813959129/183781250000000000000000000000000 : ℝ)*base76 + (936188549688334129/183781250000000000000000000000000 : ℝ)*base78 + (2493102497505052879/183781250000000000000000000000000 : ℝ)*base80 + (2337644331439/2940500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9339/2000000000000000000 : ℝ)*base90 + (9339/2000000000000000000 : ℝ)*base92 + (9339/2000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29113/50000 : ℝ) ≤ (428055497198255319592208167008351/735125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35600999/100000000000000 : ℝ)*(lower1) + (9330719/100000000000000 : ℝ)*(lower3) + (36736933/100000000000000 : ℝ)*(upper4) + (1574439/4000000000000 : ℝ)*(lower5) + (443202732758373/25000000000000 : ℝ)*(major0) + (443202732758373/25000000000000 : ℝ)*(major1) + (443202732758373/25000000000000 : ℝ)*(major2) + (2503550056007483/100000000000000 : ℝ)*(sp0) + (125176197295407/5000000000000 : ℝ)*(sp1) + (2503549868348181/100000000000000 : ℝ)*(sp2) + (255665333713571/25000000000000 : ℝ)*(sp3) + (93829651/50000000000000 : ℝ)*(sp6) + (26110099343/100000000000000 : ℝ)*(sp9) + (824446801/100000000000000 : ℝ)*(sp11) + (255665539825271/25000000000000 : ℝ)*(f.failure) + (2503550056007483/100000000000000 : ℝ)*(f.sum) + (38002261185581/5881000000000000000000000000 : ℝ)*base66 + (7752185958819038883/1470250000000000000000000000000000 : ℝ)*base68 + (8927591105481211117/1470250000000000000000000000000000 : ℝ)*base69 + (8653731102792038883/1470250000000000000000000000000000 : ℝ)*base72 + (4984475443137/1176200000000000000000000000 : ℝ)*base74 + (1874847949288961117/1470250000000000000000000000000000 : ℝ)*base75 + (3151451153612038883/1470250000000000000000000000000000 : ℝ)*base78 + (1417022831545538883/1470250000000000000000000000000000 : ℝ)*base80 + (81124480177/14702500000000000000000000 : ℝ)*base82 + (354179/50000000000000000000 : ℝ)*base90 + (354179/50000000000000000000 : ℝ)*base92 + (354179/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80493/100000 : ℝ) ≤ (1183491280415930552721775828695033/1470250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4849907/12500000000000 : ℝ)*(lower3) + (35922863/25000000000000 : ℝ)*(upper4) + (22743157/100000000000000 : ℝ)*(lower5) + (1877365840166341/100000000000000 : ℝ)*(major0) + (1877365840166341/100000000000000 : ℝ)*(major1) + (1877365840166341/100000000000000 : ℝ)*(major2) + (812280441/50000000000000 : ℝ)*(sp0) + (3387479003/10000000000000 : ℝ)*(sp1) + (8548162519/12500000000000 : ℝ)*(sp2) + (29802148857/100000000000000 : ℝ)*(sp3) + (165307654346907/6250000000000 : ℝ)*(sp8) + (2644890219321363/100000000000000 : ℝ)*(sp9) + (1322427854405621/50000000000000 : ℝ)*(sp10) + (8663566482899/800000000000 : ℝ)*(sp11) + (1082975612511233/100000000000000 : ℝ)*(f.failure) + (1322462047055697/50000000000000 : ℝ)*(f.sum) + (37099722611667/5881000000000000000000000000 : ℝ)*base65 + (42937154732373934989/5881000000000000000000000000000000 : ℝ)*base67 + (17514642273326065011/5881000000000000000000000000000000 : ℝ)*base70 + (57094608762962934989/5881000000000000000000000000000000 : ℝ)*base71 + (10071035511131/1176200000000000000000000000 : ℝ)*base73 + (38653693237517934989/5881000000000000000000000000000000 : ℝ)*base75 + (10770484233302934989/5881000000000000000000000000000000 : ℝ)*base77 + (8650695044037934989/5881000000000000000000000000000000 : ℝ)*base79 + (10229806449859/2940500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (883883/200000000000000000000 : ℝ)*base89 + (883883/200000000000000000000 : ℝ)*base91 + (883883/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-17571/20000 : ℝ) ≤ (-645825843975748816314347698561617/735125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288934677/100000000000000 : ℝ)*(lower1) + (102055937/25000000000000 : ℝ)*(lower2) + (33886183/25000000000000 : ℝ)*(lower3) + (112460951/100000000000000 : ℝ)*(upper5) + (479892408761903/25000000000000 : ℝ)*(major0) + (479892408761903/25000000000000 : ℝ)*(major1) + (479892408761903/25000000000000 : ℝ)*(major2) + (31161426241/10000000000000 : ℝ)*(sp5) + (343275240289/100000000000000 : ℝ)*(sp6) + (41799392601/100000000000000 : ℝ)*(sp7) + (1380551093546307/50000000000000 : ℝ)*(sp12) + (690197643207551/25000000000000 : ℝ)*(sp13) + (1380379455926163/50000000000000 : ℝ)*(sp14) + (1107279457230167/100000000000000 : ℝ)*(sp15) + (69207578538923/6250000000000 : ℝ)*(f.failure) + (1380551093546307/50000000000000 : ℝ)*(f.sum) + (5067050731939/1470250000000000000000000000 : ℝ)*base66 + (8074078301239673513/1470250000000000000000000000000000 : ℝ)*base68 + (8593021747670923513/1470250000000000000000000000000000 : ℝ)*base70 + (5435005402645423513/1470250000000000000000000000000000 : ℝ)*base72 + (8444737156371/5881000000000000000000000000 : ℝ)*base74 + (23878593936686423513/1470250000000000000000000000000000 : ℝ)*base76 + (19455682374195173513/1470250000000000000000000000000000 : ℝ)*base78 + (15871529305810923513/1470250000000000000000000000000000 : ℝ)*base80 + (3193683821203/235240000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (26073/12500000000000000000 : ℝ)*base89 + (26073/12500000000000000000 : ℝ)*base91 + (26073/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1613_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64929/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29113/50000 : ℝ) else (80493/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17571/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1613_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1613_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64929/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29113/50000 : ℝ) else (80493/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17571/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1613_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2091/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64929/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29113/50000 : ℝ) else (80493/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17571/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1613_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
