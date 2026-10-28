-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:07.014343+00:00
-- url     : https://prove2.me/submissions/d0355b8c-e41a-437c-9868-fe3da7fbaa8d

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
theorem support_rectangle_w1192_s6_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071589183/5000000000 : ℝ)*x 0 + (674048587/1250000000 : ℝ)*x 1 + (5266261683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071589183/5000000000 : ℝ)^8385 ≤ (2605546683267/20000000000000 : ℝ)^6337 := by
    have hnat : (1071589183 : ℕ)^8385*20000000000000^6337 ≤ 2605546683267^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071589183 5000000000 2605546683267 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674048587/1250000000 : ℝ)^8385 ≤ (5520874748893/12500000000000 : ℝ)^6337 := by
    have hnat : (674048587 : ℕ)^8385*12500000000000^6337 ≤ 5520874748893^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674048587 1250000000 5520874748893 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266261683/10000000000 : ℝ)^8385 ≤ (8561053713147/20000000000000 : ℝ)^6337 := by
    have hnat : (5266261683 : ℕ)^8385*20000000000000^6337 ≤ 8561053713147^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266261683 10000000000 8561053713147 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071589183/5000000000 : ℝ), (674048587/1250000000 : ℝ), (5266261683/10000000000 : ℝ)] ![(2605546683267/20000000000000 : ℝ), (5520874748893/12500000000000 : ℝ), (8561053713147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071589183/5000000000 : ℝ)|^8385 ≤ (2605546683267/20000000000000 : ℝ)^6337
        have hw : |(-1071589183/5000000000 : ℝ)|=(1071589183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674048587/1250000000 : ℝ)|^8385 ≤ (5520874748893/12500000000000 : ℝ)^6337
        have hw : |(674048587/1250000000 : ℝ)|=(674048587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266261683/10000000000 : ℝ)|^8385 ≤ (8561053713147/20000000000000 : ℝ)^6337
        have hw : |(5266261683/10000000000 : ℝ)|=(5266261683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668077583/1250000000 : ℝ)*x 0 + (-2207143611/10000000000 : ℝ)*x 1 + (1316565433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668077583/1250000000 : ℝ)^8385 ≤ (349200369631/800000000000 : ℝ)^6337 := by
    have hnat : (668077583 : ℕ)^8385*800000000000^6337 ≤ 349200369631^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668077583 1250000000 349200369631 800000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207143611/10000000000 : ℝ)^8385 ≤ (2708936936867/20000000000000 : ℝ)^6337 := by
    have hnat : (2207143611 : ℕ)^8385*20000000000000^6337 ≤ 2708936936867^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207143611 10000000000 2708936936867 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316565433/2500000000 : ℝ)^8385 ≤ (8561053818547/20000000000000 : ℝ)^6337 := by
    have hnat : (1316565433 : ℕ)^8385*20000000000000^6337 ≤ 8561053818547^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316565433 2500000000 8561053818547 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668077583/1250000000 : ℝ), (-2207143611/10000000000 : ℝ), (1316565433/2500000000 : ℝ)] ![(349200369631/800000000000 : ℝ), (2708936936867/20000000000000 : ℝ), (8561053818547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668077583/1250000000 : ℝ)|^8385 ≤ (349200369631/800000000000 : ℝ)^6337
        have hw : |(668077583/1250000000 : ℝ)|=(668077583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207143611/10000000000 : ℝ)|^8385 ≤ (2708936936867/20000000000000 : ℝ)^6337
        have hw : |(-2207143611/10000000000 : ℝ)|=(2207143611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316565433/2500000000 : ℝ)|^8385 ≤ (8561053818547/20000000000000 : ℝ)^6337
        have hw : |(1316565433/2500000000 : ℝ)|=(1316565433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068924151/2000000000 : ℝ)*x 0 + (5266261589/10000000000 : ℝ)*x 1 + (-1724331/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068924151/2000000000 : ℝ)^8385 ≤ (5456255898409/12500000000000 : ℝ)^6337 := by
    have hnat : (1068924151 : ℕ)^8385*12500000000000^6337 ≤ 5456255898409^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068924151 2000000000 5456255898409 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266261589/10000000000 : ℝ)^8385 ≤ (10701316888689/25000000000000 : ℝ)^6337 := by
    have hnat : (5266261589 : ℕ)^8385*25000000000000^6337 ≤ 10701316888689^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266261589 10000000000 10701316888689 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724331/7812500 : ℝ)^8385 ≤ (13544685244617/100000000000000 : ℝ)^6337 := by
    have hnat : (1724331 : ℕ)^8385*100000000000000^6337 ≤ 13544685244617^6337*7812500^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724331 7812500 13544685244617 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068924151/2000000000 : ℝ), (5266261589/10000000000 : ℝ), (-1724331/7812500 : ℝ)] ![(5456255898409/12500000000000 : ℝ), (10701316888689/25000000000000 : ℝ), (13544685244617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068924151/2000000000 : ℝ)|^8385 ≤ (5456255898409/12500000000000 : ℝ)^6337
        have hw : |(1068924151/2000000000 : ℝ)|=(1068924151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266261589/10000000000 : ℝ)|^8385 ≤ (10701316888689/25000000000000 : ℝ)^6337
        have hw : |(5266261589/10000000000 : ℝ)|=(5266261589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1724331/7812500 : ℝ)|^8385 ≤ (13544685244617/100000000000000 : ℝ)^6337
        have hw : |(-1724331/7812500 : ℝ)|=(1724331/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357663601/10000000000 : ℝ)*x 0 + (4133574/9765625 : ℝ)*x 1 + (4486169837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357663601/10000000000 : ℝ)^8385 ≤ (8329275860629/25000000000000 : ℝ)^6337 := by
    have hnat : (4357663601 : ℕ)^8385*25000000000000^6337 ≤ 8329275860629^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357663601 10000000000 8329275860629 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4133574/9765625 : ℝ)^8385 ≤ (6411919524577/20000000000000 : ℝ)^6337 := by
    have hnat : (4133574 : ℕ)^8385*20000000000000^6337 ≤ 6411919524577^6337*9765625^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133574 9765625 6411919524577 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486169837/10000000000 : ℝ)^8385 ≤ (34623298914541/100000000000000 : ℝ)^6337 := by
    have hnat : (4486169837 : ℕ)^8385*100000000000000^6337 ≤ 34623298914541^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486169837 10000000000 34623298914541 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357663601/10000000000 : ℝ), (4133574/9765625 : ℝ), (4486169837/10000000000 : ℝ)] ![(8329275860629/25000000000000 : ℝ), (6411919524577/20000000000000 : ℝ), (34623298914541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357663601/10000000000 : ℝ)|^8385 ≤ (8329275860629/25000000000000 : ℝ)^6337
        have hw : |(4357663601/10000000000 : ℝ)|=(4357663601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4133574/9765625 : ℝ)|^8385 ≤ (6411919524577/20000000000000 : ℝ)^6337
        have hw : |(4133574/9765625 : ℝ)|=(4133574/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486169837/10000000000 : ℝ)|^8385 ≤ (34623298914541/100000000000000 : ℝ)^6337
        have hw : |(4486169837/10000000000 : ℝ)|=(4486169837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143183237/10000000000 : ℝ)*x 0 + (263329019/500000000 : ℝ)*x 1 + (5392068807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143183237/10000000000 : ℝ)^8385 ≤ (13027772594871/100000000000000 : ℝ)^6337 := by
    have hnat : (2143183237 : ℕ)^8385*100000000000000^6337 ≤ 13027772594871^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143183237 10000000000 13027772594871 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263329019/500000000 : ℝ)^8385 ≤ (10702174053743/25000000000000 : ℝ)^6337 := by
    have hnat : (263329019 : ℕ)^8385*25000000000000^6337 ≤ 10702174053743^6337*500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263329019 500000000 10702174053743 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392068807/10000000000 : ℝ)^8385 ≤ (44163531171931/100000000000000 : ℝ)^6337 := by
    have hnat : (5392068807 : ℕ)^8385*100000000000000^6337 ≤ 44163531171931^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392068807 10000000000 44163531171931 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143183237/10000000000 : ℝ), (263329019/500000000 : ℝ), (5392068807/10000000000 : ℝ)] ![(13027772594871/100000000000000 : ℝ), (10702174053743/25000000000000 : ℝ), (44163531171931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143183237/10000000000 : ℝ)|^8385 ≤ (13027772594871/100000000000000 : ℝ)^6337
        have hw : |(-2143183237/10000000000 : ℝ)|=(2143183237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263329019/500000000 : ℝ)|^8385 ≤ (10702174053743/25000000000000 : ℝ)^6337
        have hw : |(263329019/500000000 : ℝ)|=(263329019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392068807/10000000000 : ℝ)|^8385 ≤ (44163531171931/100000000000000 : ℝ)^6337
        have hw : |(5392068807/10000000000 : ℝ)|=(5392068807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312549931/10000000000 : ℝ)*x 0 + (-520334111/2500000000 : ℝ)*x 1 + (5392068837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312549931/10000000000 : ℝ)^8385 ≤ (43303808639691/100000000000000 : ℝ)^6337 := by
    have hnat : (5312549931 : ℕ)^8385*100000000000000^6337 ≤ 43303808639691^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312549931 10000000000 43303808639691 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520334111/2500000000 : ℝ)^8385 ≤ (15665824809/125000000000 : ℝ)^6337 := by
    have hnat : (520334111 : ℕ)^8385*125000000000^6337 ≤ 15665824809^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520334111 2500000000 15665824809 125000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392068837/10000000000 : ℝ)^8385 ≤ (8832706299411/20000000000000 : ℝ)^6337 := by
    have hnat : (5392068837 : ℕ)^8385*20000000000000^6337 ≤ 8832706299411^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392068837 10000000000 8832706299411 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312549931/10000000000 : ℝ), (-520334111/2500000000 : ℝ), (5392068837/10000000000 : ℝ)] ![(43303808639691/100000000000000 : ℝ), (15665824809/125000000000 : ℝ), (8832706299411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312549931/10000000000 : ℝ)|^8385 ≤ (43303808639691/100000000000000 : ℝ)^6337
        have hw : |(5312549931/10000000000 : ℝ)|=(5312549931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520334111/2500000000 : ℝ)|^8385 ≤ (15665824809/125000000000 : ℝ)^6337
        have hw : |(-520334111/2500000000 : ℝ)|=(520334111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392068837/10000000000 : ℝ)|^8385 ≤ (8832706299411/20000000000000 : ℝ)^6337
        have hw : |(5392068837/10000000000 : ℝ)|=(5392068837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062509991/2000000000 : ℝ)*x 0 + (5392068819/10000000000 : ℝ)*x 1 + (-520334109/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062509991/2000000000 : ℝ)^8385 ≤ (2706488056159/6250000000000 : ℝ)^6337 := by
    have hnat : (1062509991 : ℕ)^8385*6250000000000^6337 ≤ 2706488056159^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062509991 2000000000 2706488056159 6250000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392068819/10000000000 : ℝ)^8385 ≤ (44163531301981/100000000000000 : ℝ)^6337 := by
    have hnat : (5392068819 : ℕ)^8385*100000000000000^6337 ≤ 44163531301981^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392068819 10000000000 44163531301981 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520334109/2500000000 : ℝ)^8385 ≤ (626632989173/5000000000000 : ℝ)^6337 := by
    have hnat : (520334109 : ℕ)^8385*5000000000000^6337 ≤ 626632989173^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520334109 2500000000 626632989173 5000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062509991/2000000000 : ℝ), (5392068819/10000000000 : ℝ), (-520334109/2500000000 : ℝ)] ![(2706488056159/6250000000000 : ℝ), (44163531301981/100000000000000 : ℝ), (626632989173/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062509991/2000000000 : ℝ)|^8385 ≤ (2706488056159/6250000000000 : ℝ)^6337
        have hw : |(1062509991/2000000000 : ℝ)|=(1062509991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392068819/10000000000 : ℝ)|^8385 ≤ (44163531301981/100000000000000 : ℝ)^6337
        have hw : |(5392068819/10000000000 : ℝ)|=(5392068819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520334109/2500000000 : ℝ)|^8385 ≤ (626632989173/5000000000000 : ℝ)^6337
        have hw : |(-520334109/2500000000 : ℝ)|=(520334109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s6_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357673099/10000000000 : ℝ)*x 0 + (2242764731/5000000000 : ℝ)*x 1 + (4233422679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357673099/10000000000 : ℝ)^8385 ≤ (8329299882411/25000000000000 : ℝ)^6337 := by
    have hnat : (4357673099 : ℕ)^8385*25000000000000^6337 ≤ 8329299882411^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357673099 10000000000 8329299882411 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242764731/5000000000 : ℝ)^8385 ≤ (2163547471031/6250000000000 : ℝ)^6337 := by
    have hnat : (2242764731 : ℕ)^8385*6250000000000^6337 ≤ 2163547471031^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242764731 5000000000 2163547471031 6250000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233422679/10000000000 : ℝ)^8385 ≤ (8016510228911/25000000000000 : ℝ)^6337 := by
    have hnat : (4233422679 : ℕ)^8385*25000000000000^6337 ≤ 8016510228911^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233422679 10000000000 8016510228911 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357673099/10000000000 : ℝ), (2242764731/5000000000 : ℝ), (4233422679/10000000000 : ℝ)] ![(8329299882411/25000000000000 : ℝ), (2163547471031/6250000000000 : ℝ), (8016510228911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357673099/10000000000 : ℝ)|^8385 ≤ (8329299882411/25000000000000 : ℝ)^6337
        have hw : |(4357673099/10000000000 : ℝ)|=(4357673099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242764731/5000000000 : ℝ)|^8385 ≤ (2163547471031/6250000000000 : ℝ)^6337
        have hw : |(2242764731/5000000000 : ℝ)|=(2242764731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233422679/10000000000 : ℝ)|^8385 ≤ (8016510228911/25000000000000 : ℝ)^6337
        have hw : |(4233422679/10000000000 : ℝ)|=(4233422679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2853/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1411/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1411/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5693/50000 : ℝ) ^ (131/32 : ℝ) ≤ (3427358427842443/25000000000000000000 : ℝ) := by
    have hpowers : (5693/50000 : ℝ)^131 ≤ (3427358427842443/25000000000000000000 : ℝ)^32 := by
      have hnat : (5693 : ℕ)^131*25000000000000000000^32 ≤ 3427358427842443^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5693 50000 3427358427842443 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5693/50000 : ℝ)) (X := (3427358427842443/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (1411/10000 : ℝ) ^ (131/32 : ℝ) ≤ (8247384101580973/25000000000000000000 : ℝ) := by
    have hpowers : (1411/10000 : ℝ)^131 ≤ (8247384101580973/25000000000000000000 : ℝ)^32 := by
      have hnat : (1411 : ℕ)^131*25000000000000000000^32 ≤ 8247384101580973^32*10000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1411 10000 8247384101580973 25000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1411/10000 : ℝ)) (X := (8247384101580973/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503427358427842443/12500000000000000000 : ℝ) ≤ (10000669704479489/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (12503427358427842443/12500000000000000000 : ℝ)^32 ≤ (10000669704479489/10000000000000000 : ℝ)^131 := by
      have hnat : (12503427358427842443 : ℕ)^32*10000000000000000^131 ≤ 10000669704479489^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503427358427842443 12500000000000000000 10000669704479489 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000669704479489/10000000000000000 : ℝ)) (X := (12503427358427842443/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126459342816177927/3125000000000000000 : ℝ) ≤ (10001140536964031/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3126459342816177927/3125000000000000000 : ℝ)^32 ≤ (10001140536964031/10000000000000000 : ℝ)^131 := by
      have hnat : (3126459342816177927 : ℕ)^32*10000000000000000^131 ≤ 10001140536964031^131*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126459342816177927 3125000000000000000 10001140536964031 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001140536964031/10000000000000000 : ℝ)) (X := (3126459342816177927/3125000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508247384101580973/12500000000000000000 : ℝ) ≤ (10001611369448573/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (12508247384101580973/12500000000000000000 : ℝ)^32 ≤ (10001611369448573/10000000000000000 : ℝ)^131 := by
      have hnat : (12508247384101580973 : ℕ)^32*10000000000000000^131 ≤ 10001611369448573^131*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508247384101580973 12500000000000000000 10001611369448573 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001611369448573/10000000000000000 : ℝ)) (X := (12508247384101580973/12500000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3427358427842443/25000000000000000000 : ℝ) ≤ ((2269258539805344801/2270000000000000000 : ℝ)+2*(78472080757/45400000000000 : ℝ)*(5693/50000 : ℝ))^(131/32 : ℝ) := by
    rw [show (2269258539805344801/2270000000000000000 : ℝ)+2*(78472080757/45400000000000 : ℝ)*(5693/50000 : ℝ)=(10000669704479489/10000000000000000 : ℝ) by norm_num, show 1+2*(3427358427842443/25000000000000000000 : ℝ)=(12503427358427842443/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8247384101580973/25000000000000000000 : ℝ)+(3427358427842443/25000000000000000000 : ℝ) ≤ ((2269258539805344801/2270000000000000000 : ℝ)+(78472080757/45400000000000 : ℝ)*((1411/10000 : ℝ)+(5693/50000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (2269258539805344801/2270000000000000000 : ℝ)+(78472080757/45400000000000 : ℝ)*((1411/10000 : ℝ)+(5693/50000 : ℝ))=(10001140536964031/10000000000000000 : ℝ) by norm_num, show 1+(8247384101580973/25000000000000000000 : ℝ)+(3427358427842443/25000000000000000000 : ℝ)=(3126459342816177927/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8247384101580973/25000000000000000000 : ℝ) ≤ ((2269258539805344801/2270000000000000000 : ℝ)+2*(78472080757/45400000000000 : ℝ)*(1411/10000 : ℝ))^(131/32 : ℝ) := by
    rw [show (2269258539805344801/2270000000000000000 : ℝ)+2*(78472080757/45400000000000 : ℝ)*(1411/10000 : ℝ)=(10001611369448573/10000000000000000 : ℝ) by norm_num, show 1+2*(8247384101580973/25000000000000000000 : ℝ)=(12508247384101580973/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2269258539805344801/2270000000000000000 : ℝ)*(X 1 0+X 2 0)+(78472080757/45400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (2269258539805344801/2270000000000000000 : ℝ)) (alpha := (78472080757/45400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2269258539805344801/2270000000000000000 : ℝ)*(X 0 1+X 2 1)+(78472080757/45400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (2269258539805344801/2270000000000000000 : ℝ)) (alpha := (78472080757/45400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2269258539805344801/2270000000000000000 : ℝ)*(X 0 2+X 1 2)+(78472080757/45400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (1411/10000 : ℝ)) (c := (2269258539805344801/2270000000000000000 : ℝ)) (alpha := (78472080757/45400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071589183/5000000000 : ℝ)*X 0 0+(674048587/1250000000 : ℝ)*X 0 1+(5266261683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668077583/1250000000 : ℝ)*X 1 0+(-2207143611/10000000000 : ℝ)*X 1 1+(1316565433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068924151/2000000000 : ℝ)*X 2 0+(5266261589/10000000000 : ℝ)*X 2 1+(-1724331/7812500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357663601/10000000000 : ℝ)*X 0 0+(4133574/9765625 : ℝ)*X 0 1+(4486169837/10000000000 : ℝ)*X 0 2+(4357663601/10000000000 : ℝ)*X 1 0+(4133574/9765625 : ℝ)*X 1 1+(4486169837/10000000000 : ℝ)*X 1 2+(4357663601/10000000000 : ℝ)*X 2 0+(4133574/9765625 : ℝ)*X 2 1+(4486169837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2143183237/10000000000 : ℝ)*X 0 0+(263329019/500000000 : ℝ)*X 0 1+(5392068807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312549931/10000000000 : ℝ)*X 1 0+(-520334111/2500000000 : ℝ)*X 1 1+(5392068837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062509991/2000000000 : ℝ)*X 2 0+(5392068819/10000000000 : ℝ)*X 2 1+(-520334109/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357673099/10000000000 : ℝ)*X 0 0+(2242764731/5000000000 : ℝ)*X 0 1+(4233422679/10000000000 : ℝ)*X 0 2+(4357673099/10000000000 : ℝ)*X 1 0+(2242764731/5000000000 : ℝ)*X 1 1+(4233422679/10000000000 : ℝ)*X 1 2+(4357673099/10000000000 : ℝ)*X 2 0+(2242764731/5000000000 : ℝ)*X 2 1+(4233422679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121668622947999752388508893/56750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302607231/100000000000000 : ℝ)*(base19) + (377771741/100000000000000 : ℝ)*(base23) + (75467571/100000000000000 : ℝ)*(lower2) + (8169831/6250000000000 : ℝ)*(upper3) + (869811/2000000000000 : ℝ)*(lower4) + (2968756252419723/50000000000000 : ℝ)*(major0) + (2968756252419723/50000000000000 : ℝ)*(major1) + (2968756252419723/50000000000000 : ℝ)*(major2) + (7928523937131699/100000000000000 : ℝ)*(sp0) + (7928527718461329/100000000000000 : ℝ)*(sp1) + (7928527643296819/100000000000000 : ℝ)*(sp2) + (3946488963435703/100000000000000 : ℝ)*(sp3) + (4083936861/100000000000000 : ℝ)*(sp4) + (1590741987/20000000000000 : ℝ)*(sp7) + (1973248458572819/50000000000000 : ℝ)*(f.failure) + (99106600263357/1250000000000 : ℝ)*(f.sum) + (1365159000073/141875000000000000000000000 : ℝ)*base66 + (1665893200946460123/113500000000000000000000000000000 : ℝ)*base67 + (2217289669083460123/113500000000000000000000000000000 : ℝ)*base69 + (1778533059129460123/113500000000000000000000000000000 : ℝ)*base71 + (1324790376677/567500000000000000000000000 : ℝ)*base74 + (3180839113299460123/113500000000000000000000000000000 : ℝ)*base75 + (394448695727960123/113500000000000000000000000000000 : ℝ)*base77 + (806320960201960123/113500000000000000000000000000000 : ℝ)*base79 + (2392402646251/1135000000000000000000000000 : ℝ)*base81 + (165569/25000000000000000000 : ℝ)*base89 + (165569/25000000000000000000 : ℝ)*base91 + (165569/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50370566730014832006278709/14187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (303430803/50000000000000 : ℝ)*(base19) + (68398183/10000000000000 : ℝ)*(base23) + (3799913/5000000000000 : ℝ)*(upper3) + (3836481/25000000000000 : ℝ)*(lower4) + (65381469/100000000000000 : ℝ)*(upper5) + (1491929427341497/25000000000000 : ℝ)*(major0) + (1491929427341497/25000000000000 : ℝ)*(major1) + (1491929427341497/25000000000000 : ℝ)*(major2) + (452172351/2500000000000 : ℝ)*(sp1) + (20113408187/100000000000000 : ℝ)*(sp2) + (7968861836632247/100000000000000 : ℝ)*(sp4) + (7968843142876601/100000000000000 : ℝ)*(sp5) + (796884103924223/10000000000000 : ℝ)*(sp6) + (495821682969347/12500000000000 : ℝ)*(sp7) + (495821682969347/12500000000000 : ℝ)*(f.failure) + (7968861836632247/100000000000000 : ℝ)*(f.sum) + (7342654922017/1135000000000000000000000000 : ℝ)*base66 + (621387220410957097/56750000000000000000000000000000 : ℝ)*base67 + (670041273299207097/56750000000000000000000000000000 : ℝ)*base69 + (445589706845707097/56750000000000000000000000000000 : ℝ)*base71 + (3904659593661/567500000000000000000000000 : ℝ)*base74 + (1612066247230207097/56750000000000000000000000000000 : ℝ)*base75 + (48204173126292903/56750000000000000000000000000000 : ℝ)*base78 + (875528381603207097/56750000000000000000000000000000 : ℝ)*base79 + (1561837560091/567500000000000000000000000 : ℝ)*base82 + (97/6250000000000000000 : ℝ)*base89 + (97/6250000000000000000 : ℝ)*base91 + (97/6250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1192_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2853/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1192_s7_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143200029/10000000000 : ℝ)*x 0 + (539212953/1000000000 : ℝ)*x 1 + (1053301327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143200029/10000000000 : ℝ)^8385 ≤ (6513953828439/50000000000000 : ℝ)^6337 := by
    have hnat : (2143200029 : ℕ)^8385*50000000000000^6337 ≤ 6513953828439^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143200029 10000000000 6513953828439 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539212953/1000000000 : ℝ)^8385 ≤ (22082094628271/50000000000000 : ℝ)^6337 := by
    have hnat : (539212953 : ℕ)^8385*50000000000000^6337 ≤ 22082094628271^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539212953 1000000000 22082094628271 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053301327/2000000000 : ℝ)^8385 ≤ (42807903066957/100000000000000 : ℝ)^6337 := by
    have hnat : (1053301327 : ℕ)^8385*100000000000000^6337 ≤ 42807903066957^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053301327 2000000000 42807903066957 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143200029/10000000000 : ℝ), (539212953/1000000000 : ℝ), (1053301327/2000000000 : ℝ)] ![(6513953828439/50000000000000 : ℝ), (22082094628271/50000000000000 : ℝ), (42807903066957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143200029/10000000000 : ℝ)|^8385 ≤ (6513953828439/50000000000000 : ℝ)^6337
        have hw : |(-2143200029/10000000000 : ℝ)|=(2143200029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539212953/1000000000 : ℝ)|^8385 ≤ (22082094628271/50000000000000 : ℝ)^6337
        have hw : |(539212953/1000000000 : ℝ)|=(539212953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053301327/2000000000 : ℝ)|^8385 ≤ (42807903066957/100000000000000 : ℝ)^6337
        have hw : |(1053301327/2000000000 : ℝ)|=(1053301327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336138871/2500000000 : ℝ)*x 0 + (-1103452979/5000000000 : ℝ)*x 1 + (2633253323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336138871/2500000000 : ℝ)^8385 ≤ (872986836683/2000000000000 : ℝ)^6337 := by
    have hnat : (1336138871 : ℕ)^8385*2000000000000^6337 ≤ 872986836683^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336138871 2500000000 872986836683 2000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103452979/5000000000 : ℝ)^8385 ≤ (541710198731/4000000000000 : ℝ)^6337 := by
    have hnat : (1103452979 : ℕ)^8385*4000000000000^6337 ≤ 541710198731^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103452979 5000000000 541710198731 4000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633253323/5000000000 : ℝ)^8385 ≤ (8561580637053/20000000000000 : ℝ)^6337 := by
    have hnat : (2633253323 : ℕ)^8385*20000000000000^6337 ≤ 8561580637053^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633253323 5000000000 8561580637053 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336138871/2500000000 : ℝ), (-1103452979/5000000000 : ℝ), (2633253323/5000000000 : ℝ)] ![(872986836683/2000000000000 : ℝ), (541710198731/4000000000000 : ℝ), (8561580637053/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336138871/2500000000 : ℝ)|^8385 ≤ (872986836683/2000000000000 : ℝ)^6337
        have hw : |(1336138871/2500000000 : ℝ)|=(1336138871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103452979/5000000000 : ℝ)|^8385 ≤ (541710198731/4000000000000 : ℝ)^6337
        have hw : |(-1103452979/5000000000 : ℝ)|=(1103452979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633253323/5000000000 : ℝ)|^8385 ≤ (8561580637053/20000000000000 : ℝ)^6337
        have hw : |(2633253323/5000000000 : ℝ)|=(2633253323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336138863/2500000000 : ℝ)*x 0 + (5266506663/10000000000 : ℝ)*x 1 + (-2206905977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336138863/2500000000 : ℝ)^8385 ≤ (43649341488341/100000000000000 : ℝ)^6337 := by
    have hnat : (1336138863 : ℕ)^8385*100000000000000^6337 ≤ 43649341488341^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336138863 2500000000 43649341488341 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266506663/10000000000 : ℝ)^8385 ≤ (5350987921013/12500000000000 : ℝ)^6337 := by
    have hnat : (5266506663 : ℕ)^8385*12500000000000^6337 ≤ 5350987921013^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266506663 10000000000 5350987921013 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206905977/10000000000 : ℝ)^8385 ≤ (270855102451/2000000000000 : ℝ)^6337 := by
    have hnat : (2206905977 : ℕ)^8385*2000000000000^6337 ≤ 270855102451^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206905977 10000000000 270855102451 2000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336138863/2500000000 : ℝ), (5266506663/10000000000 : ℝ), (-2206905977/10000000000 : ℝ)] ![(43649341488341/100000000000000 : ℝ), (5350987921013/12500000000000 : ℝ), (270855102451/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336138863/2500000000 : ℝ)|^8385 ≤ (43649341488341/100000000000000 : ℝ)^6337
        have hw : |(1336138863/2500000000 : ℝ)|=(1336138863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266506663/10000000000 : ℝ)|^8385 ≤ (5350987921013/12500000000000 : ℝ)^6337
        have hw : |(5266506663/10000000000 : ℝ)|=(5266506663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206905977/10000000000 : ℝ)|^8385 ≤ (270855102451/2000000000000 : ℝ)^6337
        have hw : |(-2206905977/10000000000 : ℝ)|=(2206905977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544709531/1250000000 : ℝ)*x 0 + (1058321217/2500000000 : ℝ)*x 1 + (5607077/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544709531/1250000000 : ℝ)^8385 ≤ (208232696167/625000000000 : ℝ)^6337 := by
    have hnat : (544709531 : ℕ)^8385*625000000000^6337 ≤ 208232696167^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544709531 1250000000 208232696167 625000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058321217/2500000000 : ℝ)^8385 ≤ (32064659721687/100000000000000 : ℝ)^6337 := by
    have hnat : (1058321217 : ℕ)^8385*100000000000000^6337 ≤ 32064659721687^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058321217 2500000000 32064659721687 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5607077/12500000 : ℝ)^8385 ≤ (34618108877923/100000000000000 : ℝ)^6337 := by
    have hnat : (5607077 : ℕ)^8385*100000000000000^6337 ≤ 34618108877923^6337*12500000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607077 12500000 34618108877923 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544709531/1250000000 : ℝ), (1058321217/2500000000 : ℝ), (5607077/12500000 : ℝ)] ![(208232696167/625000000000 : ℝ), (32064659721687/100000000000000 : ℝ), (34618108877923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544709531/1250000000 : ℝ)|^8385 ≤ (208232696167/625000000000 : ℝ)^6337
        have hw : |(544709531/1250000000 : ℝ)|=(544709531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058321217/2500000000 : ℝ)|^8385 ≤ (32064659721687/100000000000000 : ℝ)^6337
        have hw : |(1058321217/2500000000 : ℝ)|=(1058321217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5607077/12500000 : ℝ)|^8385 ≤ (34618108877923/100000000000000 : ℝ)^6337
        have hw : |(5607077/12500000 : ℝ)|=(5607077/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428641073/2000000000 : ℝ)*x 0 + (5266823067/10000000000 : ℝ)*x 1 + (5391811533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428641073/2000000000 : ℝ)^8385 ≤ (13027950575653/100000000000000 : ℝ)^6337 := by
    have hnat : (428641073 : ℕ)^8385*100000000000000^6337 ≤ 13027950575653^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428641073 2000000000 13027950575653 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266823067/10000000000 : ℝ)^8385 ≤ (42811306406591/100000000000000 : ℝ)^6337 := by
    have hnat : (5266823067 : ℕ)^8385*100000000000000^6337 ≤ 42811306406591^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266823067 10000000000 42811306406591 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391811533/10000000000 : ℝ)^8385 ≤ (44160742995347/100000000000000 : ℝ)^6337 := by
    have hnat : (5391811533 : ℕ)^8385*100000000000000^6337 ≤ 44160742995347^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391811533 10000000000 44160742995347 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428641073/2000000000 : ℝ), (5266823067/10000000000 : ℝ), (5391811533/10000000000 : ℝ)] ![(13027950575653/100000000000000 : ℝ), (42811306406591/100000000000000 : ℝ), (44160742995347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428641073/2000000000 : ℝ)|^8385 ≤ (13027950575653/100000000000000 : ℝ)^6337
        have hw : |(-428641073/2000000000 : ℝ)|=(428641073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266823067/10000000000 : ℝ)|^8385 ≤ (42811306406591/100000000000000 : ℝ)^6337
        have hw : |(5266823067/10000000000 : ℝ)|=(5266823067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391811533/10000000000 : ℝ)|^8385 ≤ (44160742995347/100000000000000 : ℝ)^6337
        have hw : |(5391811533/10000000000 : ℝ)|=(5391811533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062522593/2000000000 : ℝ)*x 0 + (-1040800149/5000000000 : ℝ)*x 1 + (5391812119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062522593/2000000000 : ℝ)^8385 ≤ (21652244248781/50000000000000 : ℝ)^6337 := by
    have hnat : (1062522593 : ℕ)^8385*50000000000000^6337 ≤ 21652244248781^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062522593 2000000000 21652244248781 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040800149/5000000000 : ℝ)^8385 ≤ (783422633659/6250000000000 : ℝ)^6337 := by
    have hnat : (1040800149 : ℕ)^8385*6250000000000^6337 ≤ 783422633659^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040800149 5000000000 783422633659 6250000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391812119/10000000000 : ℝ)^8385 ≤ (11040187336501/25000000000000 : ℝ)^6337 := by
    have hnat : (5391812119 : ℕ)^8385*25000000000000^6337 ≤ 11040187336501^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391812119 10000000000 11040187336501 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062522593/2000000000 : ℝ), (-1040800149/5000000000 : ℝ), (5391812119/10000000000 : ℝ)] ![(21652244248781/50000000000000 : ℝ), (783422633659/6250000000000 : ℝ), (11040187336501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062522593/2000000000 : ℝ)|^8385 ≤ (21652244248781/50000000000000 : ℝ)^6337
        have hw : |(1062522593/2000000000 : ℝ)|=(1062522593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040800149/5000000000 : ℝ)|^8385 ≤ (783422633659/6250000000000 : ℝ)^6337
        have hw : |(-1040800149/5000000000 : ℝ)|=(1040800149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391812119/10000000000 : ℝ)|^8385 ≤ (11040187336501/25000000000000 : ℝ)^6337
        have hw : |(5391812119/10000000000 : ℝ)|=(5391812119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531261231/1000000000 : ℝ)*x 0 + (5391812613/10000000000 : ℝ)*x 1 + (-2081600513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531261231/1000000000 : ℝ)^8385 ≤ (43304481432997/100000000000000 : ℝ)^6337 := by
    have hnat : (531261231 : ℕ)^8385*100000000000000^6337 ≤ 43304481432997^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531261231 1000000000 43304481432997 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391812613/10000000000 : ℝ)^8385 ≤ (4416075469963/10000000000000 : ℝ)^6337 := by
    have hnat : (5391812613 : ℕ)^8385*10000000000000^6337 ≤ 4416075469963^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391812613 10000000000 4416075469963 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081600513/10000000000 : ℝ)^8385 ≤ (626738192581/5000000000000 : ℝ)^6337 := by
    have hnat : (2081600513 : ℕ)^8385*5000000000000^6337 ≤ 626738192581^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081600513 10000000000 626738192581 5000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531261231/1000000000 : ℝ), (5391812613/10000000000 : ℝ), (-2081600513/10000000000 : ℝ)] ![(43304481432997/100000000000000 : ℝ), (4416075469963/10000000000000 : ℝ), (626738192581/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531261231/1000000000 : ℝ)|^8385 ≤ (43304481432997/100000000000000 : ℝ)^6337
        have hw : |(531261231/1000000000 : ℝ)|=(531261231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391812613/10000000000 : ℝ)|^8385 ≤ (4416075469963/10000000000000 : ℝ)^6337
        have hw : |(5391812613/10000000000 : ℝ)|=(5391812613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081600513/10000000000 : ℝ)|^8385 ≤ (626738192581/5000000000000 : ℝ)^6337
        have hw : |(-2081600513/10000000000 : ℝ)|=(2081600513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s7_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871537251/2000000000 : ℝ)*x 0 + (2242512931/5000000000 : ℝ)*x 1 + (1058480621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871537251/2000000000 : ℝ)^8385 ≤ (33317332623277/100000000000000 : ℝ)^6337 := by
    have hnat : (871537251 : ℕ)^8385*100000000000000^6337 ≤ 33317332623277^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871537251 2000000000 33317332623277 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242512931/5000000000 : ℝ)^8385 ≤ (8652904272151/25000000000000 : ℝ)^6337 := by
    have hnat : (2242512931 : ℕ)^8385*25000000000000^6337 ≤ 8652904272151^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242512931 5000000000 8652904272151 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058480621/2500000000 : ℝ)^8385 ≤ (32071050272277/100000000000000 : ℝ)^6337 := by
    have hnat : (1058480621 : ℕ)^8385*100000000000000^6337 ≤ 32071050272277^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058480621 2500000000 32071050272277 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871537251/2000000000 : ℝ), (2242512931/5000000000 : ℝ), (1058480621/2500000000 : ℝ)] ![(33317332623277/100000000000000 : ℝ), (8652904272151/25000000000000 : ℝ), (32071050272277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871537251/2000000000 : ℝ)|^8385 ≤ (33317332623277/100000000000000 : ℝ)^6337
        have hw : |(871537251/2000000000 : ℝ)|=(871537251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242512931/5000000000 : ℝ)|^8385 ≤ (8652904272151/25000000000000 : ℝ)^6337
        have hw : |(2242512931/5000000000 : ℝ)|=(2242512931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058480621/2500000000 : ℝ)|^8385 ≤ (32071050272277/100000000000000 : ℝ)^6337
        have hw : |(1058480621/2500000000 : ℝ)|=(1058480621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2853/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11417/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2853/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2853/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2853/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2853/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2853/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2853/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2853/25000 : ℝ) ^ (131/32 : ℝ) ≤ (13838044320231313/100000000000000000000 : ℝ) := by
    have hpowers : (2853/25000 : ℝ)^131 ≤ (13838044320231313/100000000000000000000 : ℝ)^32 := by
      have hnat : (2853 : ℕ)^131*100000000000000000000^32 ≤ 13838044320231313^32*25000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2853 25000 13838044320231313 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2853/25000 : ℝ)) (X := (13838044320231313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (131/32 : ℝ) ≤ (4091484433611977/12500000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^131 ≤ (4091484433611977/12500000000000000000 : ℝ)^32 := by
      have hnat : (14083 : ℕ)^131*12500000000000000000^32 ≤ 4091484433611977^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 4091484433611977 12500000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (4091484433611977/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013838044320231313/50000000000000000000 : ℝ) ≤ (5000337993219061/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50013838044320231313/50000000000000000000 : ℝ)^32 ≤ (5000337993219061/5000000000000000 : ℝ)^131 := by
      have hnat : (50013838044320231313 : ℕ)^32*5000000000000000^131 ≤ 5000337993219061^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013838044320231313 50000000000000000000 5000337993219061 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337993219061/5000000000000000 : ℝ)) (X := (50013838044320231313/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046569919789127129/100000000000000000000 : ℝ) ≤ (2500284346425031/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100046569919789127129/100000000000000000000 : ℝ)^32 ≤ (2500284346425031/2500000000000000 : ℝ)^131 := by
      have hnat : (100046569919789127129 : ℕ)^32*2500000000000000^131 ≤ 2500284346425031^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046569919789127129 100000000000000000000 2500284346425031 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500284346425031/2500000000000000 : ℝ)) (X := (100046569919789127129/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254091484433611977/6250000000000000000 : ℝ) ≤ (5000799392481063/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (6254091484433611977/6250000000000000000 : ℝ)^32 ≤ (5000799392481063/5000000000000000 : ℝ)^131 := by
      have hnat : (6254091484433611977 : ℕ)^32*5000000000000000^131 ≤ 5000799392481063^131*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254091484433611977 6250000000000000000 5000799392481063 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000799392481063/5000000000000000 : ℝ)) (X := (6254091484433611977/6250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13838044320231313/100000000000000000000 : ℝ) ≤ ((13350637291510145107/13355000000000000000 : ℝ)+2*(230699631001/133550000000000 : ℝ)*(2853/25000 : ℝ))^(131/32 : ℝ) := by
    rw [show (13350637291510145107/13355000000000000000 : ℝ)+2*(230699631001/133550000000000 : ℝ)*(2853/25000 : ℝ)=(5000337993219061/5000000000000000 : ℝ) by norm_num, show 1+2*(13838044320231313/100000000000000000000 : ℝ)=(50013838044320231313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4091484433611977/12500000000000000000 : ℝ)+(13838044320231313/100000000000000000000 : ℝ) ≤ ((13350637291510145107/13355000000000000000 : ℝ)+(230699631001/133550000000000 : ℝ)*((14083/100000 : ℝ)+(2853/25000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (13350637291510145107/13355000000000000000 : ℝ)+(230699631001/133550000000000 : ℝ)*((14083/100000 : ℝ)+(2853/25000 : ℝ))=(2500284346425031/2500000000000000 : ℝ) by norm_num, show 1+(4091484433611977/12500000000000000000 : ℝ)+(13838044320231313/100000000000000000000 : ℝ)=(100046569919789127129/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4091484433611977/12500000000000000000 : ℝ) ≤ ((13350637291510145107/13355000000000000000 : ℝ)+2*(230699631001/133550000000000 : ℝ)*(14083/100000 : ℝ))^(131/32 : ℝ) := by
    rw [show (13350637291510145107/13355000000000000000 : ℝ)+2*(230699631001/133550000000000 : ℝ)*(14083/100000 : ℝ)=(5000799392481063/5000000000000000 : ℝ) by norm_num, show 1+2*(4091484433611977/12500000000000000000 : ℝ)=(6254091484433611977/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13350637291510145107/13355000000000000000 : ℝ)*(X 1 0+X 2 0)+(230699631001/133550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (2853/25000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (13350637291510145107/13355000000000000000 : ℝ)) (alpha := (230699631001/133550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13350637291510145107/13355000000000000000 : ℝ)*(X 0 1+X 2 1)+(230699631001/133550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (2853/25000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (13350637291510145107/13355000000000000000 : ℝ)) (alpha := (230699631001/133550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13350637291510145107/13355000000000000000 : ℝ)*(X 0 2+X 1 2)+(230699631001/133550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (2853/25000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (13350637291510145107/13355000000000000000 : ℝ)) (alpha := (230699631001/133550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2143200029/10000000000 : ℝ)*X 0 0+(539212953/1000000000 : ℝ)*X 0 1+(1053301327/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336138871/2500000000 : ℝ)*X 1 0+(-1103452979/5000000000 : ℝ)*X 1 1+(2633253323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336138863/2500000000 : ℝ)*X 2 0+(5266506663/10000000000 : ℝ)*X 2 1+(-2206905977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544709531/1250000000 : ℝ)*X 0 0+(1058321217/2500000000 : ℝ)*X 0 1+(5607077/12500000 : ℝ)*X 0 2+(544709531/1250000000 : ℝ)*X 1 0+(1058321217/2500000000 : ℝ)*X 1 1+(5607077/12500000 : ℝ)*X 1 2+(544709531/1250000000 : ℝ)*X 2 0+(1058321217/2500000000 : ℝ)*X 2 1+(5607077/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428641073/2000000000 : ℝ)*X 0 0+(5266823067/10000000000 : ℝ)*X 0 1+(5391811533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062522593/2000000000 : ℝ)*X 1 0+(-1040800149/5000000000 : ℝ)*X 1 1+(5391812119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531261231/1000000000 : ℝ)*X 2 0+(5391812613/10000000000 : ℝ)*X 2 1+(-2081600513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871537251/2000000000 : ℝ)*X 0 0+(2242512931/5000000000 : ℝ)*X 0 1+(1058480621/2500000000 : ℝ)*X 0 2+(871537251/2000000000 : ℝ)*X 1 0+(2242512931/5000000000 : ℝ)*X 1 1+(1058480621/2500000000 : ℝ)*X 1 2+(871537251/2000000000 : ℝ)*X 2 0+(2242512931/5000000000 : ℝ)*X 2 1+(1058480621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2792117499430069050471265203/667750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415761113/50000000000000 : ℝ)*(base19) + (673134419/100000000000000 : ℝ)*(base23) + (59178033/100000000000000 : ℝ)*(lower2) + (36020629/25000000000000 : ℝ)*(upper3) + (22143739/100000000000000 : ℝ)*(upper5) + (5961364596941557/100000000000000 : ℝ)*(major0) + (5961364596941557/100000000000000 : ℝ)*(major1) + (5961364596941557/100000000000000 : ℝ)*(major2) + (3980178856761291/50000000000000 : ℝ)*(sp0) + (1990094373419003/25000000000000 : ℝ)*(sp1) + (7960377652063819/100000000000000 : ℝ)*(sp2) + (1981169558372197/50000000000000 : ℝ)*(sp3) + (4122335131/20000000000000 : ℝ)*(sp4) + (11612561089/100000000000000 : ℝ)*(sp7) + (3962350729305483/100000000000000 : ℝ)*(f.failure) + (3980189162599119/50000000000000 : ℝ)*(f.sum) + (3460848650033/417343750000000000000000000 : ℝ)*base66 + (30624549979871711599/1335500000000000000000000000000000 : ℝ)*base67 + (13588161287308711599/1335500000000000000000000000000000 : ℝ)*base69 + (6295958610691711599/1335500000000000000000000000000000 : ℝ)*base71 + (6646860111143/1669375000000000000000000000 : ℝ)*base73 + (15471136884669788401/1335500000000000000000000000000000 : ℝ)*base76 + (3899971402298288401/1335500000000000000000000000000000 : ℝ)*base78 + (11307416361625711599/1335500000000000000000000000000000 : ℝ)*base79 + (58173455741999/13355000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (392233/50000000000000000000 : ℝ)*base89 + (392233/50000000000000000000 : ℝ)*base91 + (392233/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3637410290992311812517253287/667750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1146994269/50000000000000 : ℝ)*(base19) + (8707259/500000000000 : ℝ)*(base23) + (107797709/50000000000000 : ℝ)*(upper2) + (297623741/50000000000000 : ℝ)*(upper3) + (126694351/50000000000000 : ℝ)*(upper5) + (5991563941700753/100000000000000 : ℝ)*(major0) + (5991563941700753/100000000000000 : ℝ)*(major1) + (5991563941700753/100000000000000 : ℝ)*(major2) + (74275032639/100000000000000 : ℝ)*(sp1) + (15788201427/20000000000000 : ℝ)*(sp2) + (8000704320733331/100000000000000 : ℝ)*(sp4) + (8000627751712153/100000000000000 : ℝ)*(sp5) + (2000155909568599/25000000000000 : ℝ)*(sp6) + (995605845273179/25000000000000 : ℝ)*(sp7) + (995605845273179/25000000000000 : ℝ)*(f.failure) + (8000704320733331/100000000000000 : ℝ)*(f.sum) + (32223651035931/13355000000000000000000000000 : ℝ)*base65 + (6309574158476965571/1335500000000000000000000000000000 : ℝ)*base67 + (14739729597652034429/1335500000000000000000000000000000 : ℝ)*base70 + (513828508690965571/1335500000000000000000000000000000 : ℝ)*base71 + (11071867457637/6677500000000000000000000000 : ℝ)*base74 + (853326906571034429/1335500000000000000000000000000000 : ℝ)*base76 + (9781852802496465571/1335500000000000000000000000000000 : ℝ)*base77 + (634699346478965571/1335500000000000000000000000000000 : ℝ)*base79 + (38841211828349/13355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (50929/12500000000000000000 : ℝ)*base89 + (50929/12500000000000000000 : ℝ)*base91 + (50929/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1192_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2853/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1192_s8_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071601751/5000000000 : ℝ)*x 0 + (337005079/625000000 : ℝ)*x 1 + (5266552673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071601751/5000000000 : ℝ)^8385 ≤ (13027935591077/100000000000000 : ℝ)^6337 := by
    have hnat : (1071601751 : ℕ)^8385*100000000000000^6337 ≤ 13027935591077^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071601751 5000000000 13027935591077 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337005079/625000000 : ℝ)^8385 ≤ (2760229135893/6250000000000 : ℝ)^6337 := by
    have hnat : (337005079 : ℕ)^8385*6250000000000^6337 ≤ 2760229135893^6337*625000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337005079 625000000 2760229135893 6250000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266552673/10000000000 : ℝ)^8385 ≤ (42808398218049/100000000000000 : ℝ)^6337 := by
    have hnat : (5266552673 : ℕ)^8385*100000000000000^6337 ≤ 42808398218049^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266552673 10000000000 42808398218049 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071601751/5000000000 : ℝ), (337005079/625000000 : ℝ), (5266552673/10000000000 : ℝ)] ![(13027935591077/100000000000000 : ℝ), (2760229135893/6250000000000 : ℝ), (42808398218049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071601751/5000000000 : ℝ)|^8385 ≤ (13027935591077/100000000000000 : ℝ)^6337
        have hw : |(-1071601751/5000000000 : ℝ)|=(1071601751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337005079/625000000 : ℝ)|^8385 ≤ (2760229135893/6250000000000 : ℝ)^6337
        have hw : |(337005079/625000000 : ℝ)|=(337005079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266552673/10000000000 : ℝ)|^8385 ≤ (42808398218049/100000000000000 : ℝ)^6337
        have hw : |(5266552673/10000000000 : ℝ)|=(5266552673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344543487/10000000000 : ℝ)*x 0 + (-2206860969/10000000000 : ℝ)*x 1 + (1053310533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344543487/10000000000 : ℝ)^8385 ≤ (43649212188493/100000000000000 : ℝ)^6337 := by
    have hnat : (5344543487 : ℕ)^8385*100000000000000^6337 ≤ 43649212188493^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344543487 10000000000 43649212188493 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206860969/10000000000 : ℝ)^8385 ≤ (13542389670133/100000000000000 : ℝ)^6337 := by
    have hnat : (2206860969 : ℕ)^8385*100000000000000^6337 ≤ 13542389670133^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206860969 10000000000 13542389670133 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053310533/2000000000 : ℝ)^8385 ≤ (21404199066003/50000000000000 : ℝ)^6337 := by
    have hnat : (1053310533 : ℕ)^8385*50000000000000^6337 ≤ 21404199066003^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053310533 2000000000 21404199066003 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344543487/10000000000 : ℝ), (-2206860969/10000000000 : ℝ), (1053310533/2000000000 : ℝ)] ![(43649212188493/100000000000000 : ℝ), (13542389670133/100000000000000 : ℝ), (21404199066003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344543487/10000000000 : ℝ)|^8385 ≤ (43649212188493/100000000000000 : ℝ)^6337
        have hw : |(5344543487/10000000000 : ℝ)|=(5344543487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2206860969/10000000000 : ℝ)|^8385 ≤ (13542389670133/100000000000000 : ℝ)^6337
        have hw : |(-2206860969/10000000000 : ℝ)|=(2206860969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053310533/2000000000 : ℝ)|^8385 ≤ (21404199066003/50000000000000 : ℝ)^6337
        have hw : |(1053310533/2000000000 : ℝ)|=(1053310533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068908699/2000000000 : ℝ)*x 0 + (263327633/500000000 : ℝ)*x 1 + (-551715241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068908699/2000000000 : ℝ)^8385 ≤ (8729842454989/20000000000000 : ℝ)^6337 := by
    have hnat : (1068908699 : ℕ)^8385*20000000000000^6337 ≤ 8729842454989^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068908699 2000000000 8729842454989 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263327633/500000000 : ℝ)^8385 ≤ (4280839807823/10000000000000 : ℝ)^6337 := by
    have hnat : (263327633 : ℕ)^8385*10000000000000^6337 ≤ 4280839807823^6337*500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263327633 500000000 4280839807823 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551715241/2500000000 : ℝ)^8385 ≤ (2708477925907/20000000000000 : ℝ)^6337 := by
    have hnat : (551715241 : ℕ)^8385*20000000000000^6337 ≤ 2708477925907^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551715241 2500000000 2708477925907 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068908699/2000000000 : ℝ), (263327633/500000000 : ℝ), (-551715241/2500000000 : ℝ)] ![(8729842454989/20000000000000 : ℝ), (4280839807823/10000000000000 : ℝ), (2708477925907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068908699/2000000000 : ℝ)|^8385 ≤ (8729842454989/20000000000000 : ℝ)^6337
        have hw : |(1068908699/2000000000 : ℝ)|=(1068908699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263327633/500000000 : ℝ)|^8385 ≤ (4280839807823/10000000000000 : ℝ)^6337
        have hw : |(263327633/500000000 : ℝ)|=(263327633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-551715241/2500000000 : ℝ)|^8385 ≤ (2708477925907/20000000000000 : ℝ)^6337
        have hw : |(-551715241/2500000000 : ℝ)|=(551715241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8511091/19531250 : ℝ)*x 0 + (846675841/2000000000 : ℝ)*x 1 + (448556669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8511091/19531250 : ℝ)^8385 ≤ (33317255099963/100000000000000 : ℝ)^6337 := by
    have hnat : (8511091 : ℕ)^8385*100000000000000^6337 ≤ 33317255099963^6337*19531250^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8511091 19531250 33317255099963 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846675841/2000000000 : ℝ)^8385 ≤ (32065605201207/100000000000000 : ℝ)^6337 := by
    have hnat : (846675841 : ℕ)^8385*100000000000000^6337 ≤ 32065605201207^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846675841 2000000000 32065605201207 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448556669/1000000000 : ℝ)^8385 ≤ (3461713969293/10000000000000 : ℝ)^6337 := by
    have hnat : (448556669 : ℕ)^8385*10000000000000^6337 ≤ 3461713969293^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448556669 1000000000 3461713969293 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8511091/19531250 : ℝ), (846675841/2000000000 : ℝ), (448556669/1000000000 : ℝ)] ![(33317255099963/100000000000000 : ℝ), (32065605201207/100000000000000 : ℝ), (3461713969293/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8511091/19531250 : ℝ)|^8385 ≤ (33317255099963/100000000000000 : ℝ)^6337
        have hw : |(8511091/19531250 : ℝ)|=(8511091/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846675841/2000000000 : ℝ)|^8385 ≤ (32065605201207/100000000000000 : ℝ)^6337
        have hw : |(846675841/2000000000 : ℝ)|=(846675841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448556669/1000000000 : ℝ)|^8385 ≤ (3461713969293/10000000000000 : ℝ)^6337
        have hw : |(448556669/1000000000 : ℝ)|=(448556669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143208439/10000000000 : ℝ)*x 0 + (5266868713/10000000000 : ℝ)*x 1 + (5391763951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143208439/10000000000 : ℝ)^8385 ≤ (1628496912577/12500000000000 : ℝ)^6337 := by
    have hnat : (2143208439 : ℕ)^8385*12500000000000^6337 ≤ 1628496912577^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143208439 10000000000 1628496912577 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266868713/10000000000 : ℝ)^8385 ≤ (5351474668893/12500000000000 : ℝ)^6337 := by
    have hnat : (5266868713 : ℕ)^8385*12500000000000^6337 ≤ 5351474668893^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266868713 10000000000 5351474668893 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391763951/10000000000 : ℝ)^8385 ≤ (22080113667877/50000000000000 : ℝ)^6337 := by
    have hnat : (5391763951 : ℕ)^8385*50000000000000^6337 ≤ 22080113667877^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391763951 10000000000 22080113667877 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143208439/10000000000 : ℝ), (5266868713/10000000000 : ℝ), (5391763951/10000000000 : ℝ)] ![(1628496912577/12500000000000 : ℝ), (5351474668893/12500000000000 : ℝ), (22080113667877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143208439/10000000000 : ℝ)|^8385 ≤ (1628496912577/12500000000000 : ℝ)^6337
        have hw : |(-2143208439/10000000000 : ℝ)|=(2143208439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266868713/10000000000 : ℝ)|^8385 ≤ (5351474668893/12500000000000 : ℝ)^6337
        have hw : |(5266868713/10000000000 : ℝ)|=(5266868713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391763951/10000000000 : ℝ)|^8385 ≤ (22080113667877/50000000000000 : ℝ)^6337
        have hw : |(5391763951/10000000000 : ℝ)|=(5391763951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664078077/1250000000 : ℝ)*x 0 + (-2081649083/10000000000 : ℝ)*x 1 + (336985291/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664078077/1250000000 : ℝ)^8385 ≤ (4330461416057/10000000000000 : ℝ)^6337 := by
    have hnat : (664078077 : ℕ)^8385*10000000000000^6337 ≤ 4330461416057^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664078077 1250000000 4330461416057 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081649083/10000000000 : ℝ)^8385 ≤ (12535150848863/100000000000000 : ℝ)^6337 := by
    have hnat : (2081649083 : ℕ)^8385*100000000000000^6337 ≤ 12535150848863^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081649083 10000000000 12535150848863 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336985291/625000000 : ℝ)^8385 ≤ (11040058744007/25000000000000 : ℝ)^6337 := by
    have hnat : (336985291 : ℕ)^8385*25000000000000^6337 ≤ 11040058744007^6337*625000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336985291 625000000 11040058744007 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664078077/1250000000 : ℝ), (-2081649083/10000000000 : ℝ), (336985291/625000000 : ℝ)] ![(4330461416057/10000000000000 : ℝ), (12535150848863/100000000000000 : ℝ), (11040058744007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664078077/1250000000 : ℝ)|^8385 ≤ (4330461416057/10000000000000 : ℝ)^6337
        have hw : |(664078077/1250000000 : ℝ)|=(664078077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2081649083/10000000000 : ℝ)|^8385 ≤ (12535150848863/100000000000000 : ℝ)^6337
        have hw : |(-2081649083/10000000000 : ℝ)|=(2081649083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336985291/625000000 : ℝ)|^8385 ≤ (11040058744007/25000000000000 : ℝ)^6337
        have hw : |(336985291/625000000 : ℝ)|=(336985291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656312521/5000000000 : ℝ)*x 0 + (2695882043/5000000000 : ℝ)*x 1 + (-1040824641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656312521/5000000000 : ℝ)^8385 ≤ (10826154688809/25000000000000 : ℝ)^6337 := by
    have hnat : (2656312521 : ℕ)^8385*25000000000000^6337 ≤ 10826154688809^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656312521 5000000000 10826154688809 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695882043/5000000000 : ℝ)^8385 ≤ (8832045759757/20000000000000 : ℝ)^6337 := by
    have hnat : (2695882043 : ℕ)^8385*20000000000000^6337 ≤ 8832045759757^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695882043 5000000000 8832045759757 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040824641/5000000000 : ℝ)^8385 ≤ (6267576217233/50000000000000 : ℝ)^6337 := by
    have hnat : (1040824641 : ℕ)^8385*50000000000000^6337 ≤ 6267576217233^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040824641 5000000000 6267576217233 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656312521/5000000000 : ℝ), (2695882043/5000000000 : ℝ), (-1040824641/5000000000 : ℝ)] ![(10826154688809/25000000000000 : ℝ), (8832045759757/20000000000000 : ℝ), (6267576217233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656312521/5000000000 : ℝ)|^8385 ≤ (10826154688809/25000000000000 : ℝ)^6337
        have hw : |(2656312521/5000000000 : ℝ)|=(2656312521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695882043/5000000000 : ℝ)|^8385 ≤ (8832045759757/20000000000000 : ℝ)^6337
        have hw : |(2695882043/5000000000 : ℝ)|=(2695882043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040824641/5000000000 : ℝ)|^8385 ≤ (6267576217233/50000000000000 : ℝ)^6337
        have hw : |(-1040824641/5000000000 : ℝ)|=(1040824641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s8_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089422009/2500000000 : ℝ)*x 0 + (4484932549/10000000000 : ℝ)*x 1 + (4234015753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089422009/2500000000 : ℝ)^8385 ≤ (33317350640903/100000000000000 : ℝ)^6337 := by
    have hnat : (1089422009 : ℕ)^8385*100000000000000^6337 ≤ 33317350640903^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089422009 2500000000 33317350640903 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484932549/10000000000 : ℝ)^8385 ≤ (8652666063791/25000000000000 : ℝ)^6337 := by
    have hnat : (4484932549 : ℕ)^8385*25000000000000^6337 ≤ 8652666063791^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484932549 10000000000 8652666063791 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234015753/10000000000 : ℝ)^8385 ≤ (125281191771/390625000000 : ℝ)^6337 := by
    have hnat : (4234015753 : ℕ)^8385*390625000000^6337 ≤ 125281191771^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234015753 10000000000 125281191771 390625000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089422009/2500000000 : ℝ), (4484932549/10000000000 : ℝ), (4234015753/10000000000 : ℝ)] ![(33317350640903/100000000000000 : ℝ), (8652666063791/25000000000000 : ℝ), (125281191771/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089422009/2500000000 : ℝ)|^8385 ≤ (33317350640903/100000000000000 : ℝ)^6337
        have hw : |(1089422009/2500000000 : ℝ)|=(1089422009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484932549/10000000000 : ℝ)|^8385 ≤ (8652666063791/25000000000000 : ℝ)^6337
        have hw : |(4484932549/10000000000 : ℝ)|=(4484932549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234015753/10000000000 : ℝ)|^8385 ≤ (125281191771/390625000000 : ℝ)^6337
        have hw : |(4234015753/10000000000 : ℝ)|=(4234015753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5709/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11417/100000 : ℝ) ^ (131/32 : ℝ) ≤ (13862881289796613/100000000000000000000 : ℝ) := by
    have hpowers : (11417/100000 : ℝ)^131 ≤ (13862881289796613/100000000000000000000 : ℝ)^32 := by
      have hnat : (11417 : ℕ)^131*100000000000000000000^32 ≤ 13862881289796613^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11417 100000 13862881289796613 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11417/100000 : ℝ)) (X := (13862881289796613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/50000 : ℝ) ^ (131/32 : ℝ) ≤ (163421639392961/500000000000000000 : ℝ) := by
    have hpowers : (7039/50000 : ℝ)^131 ≤ (163421639392961/500000000000000000 : ℝ)^32 := by
      have hnat : (7039 : ℕ)^131*500000000000000000^32 ≤ 163421639392961^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 50000 163421639392961 500000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/50000 : ℝ)) (X := (163421639392961/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013862881289796613/50000000000000000000 : ℝ) ≤ (2000135439918673/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50013862881289796613/50000000000000000000 : ℝ)^32 ≤ (2000135439918673/2000000000000000 : ℝ)^131 := by
      have hnat : (50013862881289796613 : ℕ)^32*2000000000000000^131 ≤ 2000135439918673^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013862881289796613 50000000000000000000 2000135439918673 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000135439918673/2000000000000000 : ℝ)) (X := (50013862881289796613/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046547209168388813/100000000000000000000 : ℝ) ≤ (5000568415565993/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100046547209168388813/100000000000000000000 : ℝ)^32 ≤ (5000568415565993/5000000000000000 : ℝ)^131 := by
      have hnat : (100046547209168388813 : ℕ)^32*5000000000000000^131 ≤ 5000568415565993^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046547209168388813 100000000000000000000 5000568415565993 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000568415565993/5000000000000000 : ℝ)) (X := (100046547209168388813/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (250163421639392961/250000000000000000 : ℝ) ≤ (10001596462670607/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (250163421639392961/250000000000000000 : ℝ)^32 ≤ (10001596462670607/10000000000000000 : ℝ)^131 := by
      have hnat : (250163421639392961 : ℕ)^32*10000000000000000^131 ≤ 10001596462670607^131*250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250163421639392961 250000000000000000 10001596462670607 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001596462670607/10000000000000000 : ℝ)) (X := (250163421639392961/250000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13862881289796613/100000000000000000000 : ℝ) ≤ ((26601306801565072351/26610000000000000000 : ℝ)+2*(459631538621/266100000000000 : ℝ)*(11417/100000 : ℝ))^(131/32 : ℝ) := by
    rw [show (26601306801565072351/26610000000000000000 : ℝ)+2*(459631538621/266100000000000 : ℝ)*(11417/100000 : ℝ)=(2000135439918673/2000000000000000 : ℝ) by norm_num, show 1+2*(13862881289796613/100000000000000000000 : ℝ)=(50013862881289796613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(163421639392961/500000000000000000 : ℝ)+(13862881289796613/100000000000000000000 : ℝ) ≤ ((26601306801565072351/26610000000000000000 : ℝ)+(459631538621/266100000000000 : ℝ)*((7039/50000 : ℝ)+(11417/100000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (26601306801565072351/26610000000000000000 : ℝ)+(459631538621/266100000000000 : ℝ)*((7039/50000 : ℝ)+(11417/100000 : ℝ))=(5000568415565993/5000000000000000 : ℝ) by norm_num, show 1+(163421639392961/500000000000000000 : ℝ)+(13862881289796613/100000000000000000000 : ℝ)=(100046547209168388813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(163421639392961/500000000000000000 : ℝ) ≤ ((26601306801565072351/26610000000000000000 : ℝ)+2*(459631538621/266100000000000 : ℝ)*(7039/50000 : ℝ))^(131/32 : ℝ) := by
    rw [show (26601306801565072351/26610000000000000000 : ℝ)+2*(459631538621/266100000000000 : ℝ)*(7039/50000 : ℝ)=(10001596462670607/10000000000000000 : ℝ) by norm_num, show 1+2*(163421639392961/500000000000000000 : ℝ)=(250163421639392961/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26601306801565072351/26610000000000000000 : ℝ)*(X 1 0+X 2 0)+(459631538621/266100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (26601306801565072351/26610000000000000000 : ℝ)) (alpha := (459631538621/266100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26601306801565072351/26610000000000000000 : ℝ)*(X 0 1+X 2 1)+(459631538621/266100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (26601306801565072351/26610000000000000000 : ℝ)) (alpha := (459631538621/266100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26601306801565072351/26610000000000000000 : ℝ)*(X 0 2+X 1 2)+(459631538621/266100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (26601306801565072351/26610000000000000000 : ℝ)) (alpha := (459631538621/266100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071601751/5000000000 : ℝ)*X 0 0+(337005079/625000000 : ℝ)*X 0 1+(5266552673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344543487/10000000000 : ℝ)*X 1 0+(-2206860969/10000000000 : ℝ)*X 1 1+(1053310533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068908699/2000000000 : ℝ)*X 2 0+(263327633/500000000 : ℝ)*X 2 1+(-551715241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((8511091/19531250 : ℝ)*X 0 0+(846675841/2000000000 : ℝ)*X 0 1+(448556669/1000000000 : ℝ)*X 0 2+(8511091/19531250 : ℝ)*X 1 0+(846675841/2000000000 : ℝ)*X 1 1+(448556669/1000000000 : ℝ)*X 1 2+(8511091/19531250 : ℝ)*X 2 0+(846675841/2000000000 : ℝ)*X 2 1+(448556669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2143208439/10000000000 : ℝ)*X 0 0+(5266868713/10000000000 : ℝ)*X 0 1+(5391763951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664078077/1250000000 : ℝ)*X 1 0+(-2081649083/10000000000 : ℝ)*X 1 1+(336985291/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656312521/5000000000 : ℝ)*X 2 0+(2695882043/5000000000 : ℝ)*X 2 1+(-1040824641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089422009/2500000000 : ℝ)*X 0 0+(4484932549/10000000000 : ℝ)*X 0 1+(4234015753/10000000000 : ℝ)*X 0 2+(1089422009/2500000000 : ℝ)*X 1 0+(4484932549/10000000000 : ℝ)*X 1 1+(4234015753/10000000000 : ℝ)*X 1 2+(1089422009/2500000000 : ℝ)*X 2 0+(4484932549/10000000000 : ℝ)*X 2 1+(4234015753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1763074779148135337053819413/443500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184028677/25000000000000 : ℝ)*(base19) + (87248773/12500000000000 : ℝ)*(base23) + (26748901/100000000000000 : ℝ)*(lower2) + (22879657/25000000000000 : ℝ)*(upper3) + (32139011/50000000000000 : ℝ)*(upper5) + (5965838876856363/100000000000000 : ℝ)*(major0) + (5965838876856363/100000000000000 : ℝ)*(major1) + (5965838876856363/100000000000000 : ℝ)*(major2) + (7966332954642291/100000000000000 : ℝ)*(sp0) + (3983176114125807/50000000000000 : ℝ)*(sp1) + (3983176133188069/50000000000000 : ℝ)*(sp2) + (991328440857743/25000000000000 : ℝ)*(sp3) + (156325969/781250000000 : ℝ)*(sp4) + (5446701613/50000000000000 : ℝ)*(sp7) + (3965324656834197/100000000000000 : ℝ)*(f.failure) + (3983176482183161/50000000000000 : ℝ)*(f.sum) + (33293058051909/4435000000000000000000000000 : ℝ)*base66 + (7945392646913993529/887000000000000000000000000000000 : ℝ)*base68 + (10822482840946993529/887000000000000000000000000000000 : ℝ)*base70 + (17375006804661993529/887000000000000000000000000000000 : ℝ)*base72 + (1332140323061/4435000000000000000000000000 : ℝ)*base73 + (11014226859008006471/887000000000000000000000000000000 : ℝ)*base75 + (3688760271665993529/887000000000000000000000000000000 : ℝ)*base78 + (10578466602806006471/887000000000000000000000000000000 : ℝ)*base79 + (17074788138169/4435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (27447/50000000000000000000 : ℝ)*base89 + (27447/50000000000000000000 : ℝ)*base91 + (27447/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2977184396480480889156802503/443500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9760319/781250000000 : ℝ)*(base19) + (2242356733/100000000000000 : ℝ)*(base23) + (154894489/20000000000000 : ℝ)*(lower1) + (71397387/50000000000000 : ℝ)*(upper2) + (365711603/100000000000000 : ℝ)*(upper3) + (5996003632452953/100000000000000 : ℝ)*(major0) + (5996003632452953/100000000000000 : ℝ)*(major1) + (5996003632452953/100000000000000 : ℝ)*(major2) + (13686585727/100000000000000 : ℝ)*(sp2) + (1066289819/20000000000000 : ℝ)*(sp3) + (8006632722959903/100000000000000 : ℝ)*(sp4) + (8006631473639071/100000000000000 : ℝ)*(sp5) + (4003308397008721/50000000000000 : ℝ)*(sp6) + (996342246683143/25000000000000 : ℝ)*(sp7) + (1992687159090833/50000000000000 : ℝ)*(f.failure) + (8006632722959903/100000000000000 : ℝ)*(f.sum) + (27175868314381/6652500000000000000000000000 : ℝ)*base66 + (1317696165744032499/887000000000000000000000000000000 : ℝ)*base68 + (8315007372243032499/887000000000000000000000000000000 : ℝ)*base70 + (7146780074206032499/887000000000000000000000000000000 : ℝ)*base72 + (22463273183237/13305000000000000000000000000 : ℝ)*base74 + (11601003381244032499/887000000000000000000000000000000 : ℝ)*base76 + (1317234089102967501/887000000000000000000000000000000 : ℝ)*base77 + (7180777681464967501/887000000000000000000000000000000 : ℝ)*base79 + (84038562836357/13305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (34917/25000000000000000000 : ℝ)*base90 + (34917/25000000000000000000 : ℝ)*base92 + (34917/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1192_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1192_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1192_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1192_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1192_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1411/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
