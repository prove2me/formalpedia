-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1507_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:20.559222+00:00
-- url     : https://prove2.me/submissions/69264c71-87d4-4f6e-b05f-a84b71665555

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
theorem support_rectangle_w1507_s6_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070373333/2000000000 : ℝ)*x 0 + (5217381979/10000000000 : ℝ)*x 1 + (-1986321789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070373333/2000000000 : ℝ)^4511 ≤ (111357011057/250000000000 : ℝ)^3487 := by
    have hnat : (1070373333 : ℕ)^4511*250000000000^3487 ≤ 111357011057^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070373333 2000000000 111357011057 250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217381979/10000000000 : ℝ)^4511 ≤ (21550093776853/50000000000000 : ℝ)^3487 := by
    have hnat : (5217381979 : ℕ)^4511*50000000000000^3487 ≤ 21550093776853^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217381979 10000000000 21550093776853 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986321789/10000000000 : ℝ)^4511 ≤ (12357008010819/100000000000000 : ℝ)^3487 := by
    have hnat : (1986321789 : ℕ)^4511*100000000000000^3487 ≤ 12357008010819^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986321789 10000000000 12357008010819 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070373333/2000000000 : ℝ), (5217381979/10000000000 : ℝ), (-1986321789/10000000000 : ℝ)] ![(111357011057/250000000000 : ℝ), (21550093776853/50000000000000 : ℝ), (12357008010819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070373333/2000000000 : ℝ)|^4511 ≤ (111357011057/250000000000 : ℝ)^3487
        have hw : |(1070373333/2000000000 : ℝ)|=(1070373333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217381979/10000000000 : ℝ)|^4511 ≤ (21550093776853/50000000000000 : ℝ)^3487
        have hw : |(5217381979/10000000000 : ℝ)|=(5217381979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986321789/10000000000 : ℝ)|^4511 ≤ (12357008010819/100000000000000 : ℝ)^3487
        have hw : |(-1986321789/10000000000 : ℝ)|=(1986321789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s6_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875459199/10000000000 : ℝ)*x 0 + (1043698971/2000000000 : ℝ)*x 1 + (2716380461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875459199/10000000000 : ℝ)^4511 ≤ (11472203024269/100000000000000 : ℝ)^3487 := by
    have hnat : (1875459199 : ℕ)^4511*100000000000000^3487 ≤ 11472203024269^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875459199 10000000000 11472203024269 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043698971/2000000000 : ℝ)^4511 ≤ (43112081001853/100000000000000 : ℝ)^3487 := by
    have hnat : (1043698971 : ℕ)^4511*100000000000000^3487 ≤ 43112081001853^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043698971 2000000000 43112081001853 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716380461/5000000000 : ℝ)^4511 ≤ (2838482247677/6250000000000 : ℝ)^3487 := by
    have hnat : (2716380461 : ℕ)^4511*6250000000000^3487 ≤ 2838482247677^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716380461 5000000000 2838482247677 6250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875459199/10000000000 : ℝ), (1043698971/2000000000 : ℝ), (2716380461/5000000000 : ℝ)] ![(11472203024269/100000000000000 : ℝ), (43112081001853/100000000000000 : ℝ), (2838482247677/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875459199/10000000000 : ℝ)|^4511 ≤ (11472203024269/100000000000000 : ℝ)^3487
        have hw : |(-1875459199/10000000000 : ℝ)|=(1875459199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043698971/2000000000 : ℝ)|^4511 ≤ (43112081001853/100000000000000 : ℝ)^3487
        have hw : |(1043698971/2000000000 : ℝ)|=(1043698971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716380461/5000000000 : ℝ)|^4511 ≤ (2838482247677/6250000000000 : ℝ)^3487
        have hw : |(2716380461/5000000000 : ℝ)|=(2716380461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s6_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295075607/10000000000 : ℝ)*x 0 + (-442735577/2500000000 : ℝ)*x 1 + (2716380833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295075607/10000000000 : ℝ)^4511 ≤ (43932292412127/100000000000000 : ℝ)^3487 := by
    have hnat : (5295075607 : ℕ)^4511*100000000000000^3487 ≤ 43932292412127^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295075607 10000000000 43932292412127 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442735577/2500000000 : ℝ)^4511 ≤ (2662995888247/25000000000000 : ℝ)^3487 := by
    have hnat : (442735577 : ℕ)^4511*25000000000000^3487 ≤ 2662995888247^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442735577 2500000000 2662995888247 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716380833/5000000000 : ℝ)^4511 ≤ (45415724008821/100000000000000 : ℝ)^3487 := by
    have hnat : (2716380833 : ℕ)^4511*100000000000000^3487 ≤ 45415724008821^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716380833 5000000000 45415724008821 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295075607/10000000000 : ℝ), (-442735577/2500000000 : ℝ), (2716380833/5000000000 : ℝ)] ![(43932292412127/100000000000000 : ℝ), (2662995888247/25000000000000 : ℝ), (45415724008821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295075607/10000000000 : ℝ)|^4511 ≤ (43932292412127/100000000000000 : ℝ)^3487
        have hw : |(5295075607/10000000000 : ℝ)|=(5295075607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442735577/2500000000 : ℝ)|^4511 ≤ (2662995888247/25000000000000 : ℝ)^3487
        have hw : |(-442735577/2500000000 : ℝ)|=(442735577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716380833/5000000000 : ℝ)|^4511 ≤ (45415724008821/100000000000000 : ℝ)^3487
        have hw : |(2716380833/5000000000 : ℝ)|=(2716380833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s6_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059015293/2000000000 : ℝ)*x 0 + (5432761429/10000000000 : ℝ)*x 1 + (-354188291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059015293/2000000000 : ℝ)^4511 ≤ (10983075405321/25000000000000 : ℝ)^3487 := by
    have hnat : (1059015293 : ℕ)^4511*25000000000000^3487 ≤ 10983075405321^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059015293 2000000000 10983075405321 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432761429/10000000000 : ℝ)^4511 ≤ (5676965180723/12500000000000 : ℝ)^3487 := by
    have hnat : (5432761429 : ℕ)^4511*12500000000000^3487 ≤ 5676965180723^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432761429 10000000000 5676965180723 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354188291/2000000000 : ℝ)^4511 ≤ (10651976915619/100000000000000 : ℝ)^3487 := by
    have hnat : (354188291 : ℕ)^4511*100000000000000^3487 ≤ 10651976915619^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354188291 2000000000 10651976915619 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059015293/2000000000 : ℝ), (5432761429/10000000000 : ℝ), (-354188291/2000000000 : ℝ)] ![(10983075405321/25000000000000 : ℝ), (5676965180723/12500000000000 : ℝ), (10651976915619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059015293/2000000000 : ℝ)|^4511 ≤ (10983075405321/25000000000000 : ℝ)^3487
        have hw : |(1059015293/2000000000 : ℝ)|=(1059015293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432761429/10000000000 : ℝ)|^4511 ≤ (5676965180723/12500000000000 : ℝ)^3487
        have hw : |(5432761429/10000000000 : ℝ)|=(5432761429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-354188291/2000000000 : ℝ)|^4511 ≤ (10651976915619/100000000000000 : ℝ)^3487
        have hw : |(-354188291/2000000000 : ℝ)|=(354188291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s6_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068043833/2500000000 : ℝ)*x 0 + (4520162281/10000000000 : ℝ)*x 1 + (504500799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068043833/2500000000 : ℝ)^4511 ≤ (4160012958493/12500000000000 : ℝ)^3487 := by
    have hnat : (1068043833 : ℕ)^4511*12500000000000^3487 ≤ 4160012958493^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068043833 2500000000 4160012958493 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520162281/10000000000 : ℝ)^4511 ≤ (35800229347969/100000000000000 : ℝ)^3487 := by
    have hnat : (4520162281 : ℕ)^4511*100000000000000^3487 ≤ 35800229347969^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520162281 10000000000 35800229347969 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504500799/1250000000 : ℝ)^4511 ≤ (7729916745107/25000000000000 : ℝ)^3487 := by
    have hnat : (504500799 : ℕ)^4511*25000000000000^3487 ≤ 7729916745107^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504500799 1250000000 7729916745107 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068043833/2500000000 : ℝ), (4520162281/10000000000 : ℝ), (504500799/1250000000 : ℝ)] ![(4160012958493/12500000000000 : ℝ), (35800229347969/100000000000000 : ℝ), (7729916745107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068043833/2500000000 : ℝ)|^4511 ≤ (4160012958493/12500000000000 : ℝ)^3487
        have hw : |(1068043833/2500000000 : ℝ)|=(1068043833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520162281/10000000000 : ℝ)|^4511 ≤ (35800229347969/100000000000000 : ℝ)^3487
        have hw : |(4520162281/10000000000 : ℝ)|=(4520162281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504500799/1250000000 : ℝ)|^4511 ≤ (7729916745107/25000000000000 : ℝ)^3487
        have hw : |(504500799/1250000000 : ℝ)|=(504500799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (681/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (681/6250 : ℝ) ^ (4509/1024 : ℝ) ≤ (5764725629549901/100000000000000000000 : ℝ) := by
    have hpowers : (681/6250 : ℝ)^4509 ≤ (5764725629549901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (681 : ℕ)^4509*100000000000000000000^1024 ≤ 5764725629549901^1024*6250^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        681 6250 5764725629549901 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (681/6250 : ℝ)) (X := (5764725629549901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4509/1024 : ℝ) ≤ (423027963344873/1562500000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4509 ≤ (423027963344873/1562500000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4509*1562500000000000000^1024 ≤ 423027963344873^1024*50000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 423027963344873 1562500000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (423027963344873/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005764725629549901/50000000000000000000 : ℝ) ≤ (312508181991639/312500000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50005764725629549901/50000000000000000000 : ℝ)^1024 ≤ (312508181991639/312500000000000 : ℝ)^4509 := by
      have hnat : (50005764725629549901 : ℕ)^1024*312500000000000^4509 ≤ 312508181991639^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005764725629549901 50000000000000000000 312508181991639 312500000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508181991639/312500000000000 : ℝ)) (X := (50005764725629549901/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032838515283621773/100000000000000000000 : ℝ) ≤ (10000745672502017/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (100032838515283621773/100000000000000000000 : ℝ)^1024 ≤ (10000745672502017/10000000000000000 : ℝ)^4509 := by
      have hnat : (100032838515283621773 : ℕ)^1024*10000000000000000^4509 ≤ 10000745672502017^4509*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032838515283621773 100000000000000000000 10000745672502017 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000745672502017/10000000000000000 : ℝ)) (X := (100032838515283621773/100000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781673027963344873/781250000000000000 : ℝ) ≤ (5000614760635793/5000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (781673027963344873/781250000000000000 : ℝ)^1024 ≤ (5000614760635793/5000000000000000 : ℝ)^4509 := by
      have hnat : (781673027963344873 : ℕ)^1024*5000000000000000^4509 ≤ 5000614760635793^4509*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781673027963344873 781250000000000000 5000614760635793 5000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000614760635793/5000000000000000 : ℝ)) (X := (781673027963344873/781250000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5764725629549901/100000000000000000000 : ℝ) ≤ ((286566604320315993/286625000000000000 : ℝ)+2*(483848769569/458600000000000 : ℝ)*(681/6250 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (286566604320315993/286625000000000000 : ℝ)+2*(483848769569/458600000000000 : ℝ)*(681/6250 : ℝ)=(312508181991639/312500000000000 : ℝ) by norm_num, show 1+2*(5764725629549901/100000000000000000000 : ℝ)=(50005764725629549901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(423027963344873/1562500000000000000 : ℝ)+(5764725629549901/100000000000000000000 : ℝ) ≤ ((286566604320315993/286625000000000000 : ℝ)+(483848769569/458600000000000 : ℝ)*((7741/50000 : ℝ)+(681/6250 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (286566604320315993/286625000000000000 : ℝ)+(483848769569/458600000000000 : ℝ)*((7741/50000 : ℝ)+(681/6250 : ℝ))=(10000745672502017/10000000000000000 : ℝ) by norm_num, show 1+(423027963344873/1562500000000000000 : ℝ)+(5764725629549901/100000000000000000000 : ℝ)=(100032838515283621773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(423027963344873/1562500000000000000 : ℝ) ≤ ((286566604320315993/286625000000000000 : ℝ)+2*(483848769569/458600000000000 : ℝ)*(7741/50000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (286566604320315993/286625000000000000 : ℝ)+2*(483848769569/458600000000000 : ℝ)*(7741/50000 : ℝ)=(5000614760635793/5000000000000000 : ℝ) by norm_num, show 1+2*(423027963344873/1562500000000000000 : ℝ)=(781673027963344873/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (286566604320315993/286625000000000000 : ℝ)*(X 1 0+X 2 0)+(483848769569/458600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (286566604320315993/286625000000000000 : ℝ)) (alpha := (483848769569/458600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (286566604320315993/286625000000000000 : ℝ)*(X 0 1+X 2 1)+(483848769569/458600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (286566604320315993/286625000000000000 : ℝ)) (alpha := (483848769569/458600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (286566604320315993/286625000000000000 : ℝ)*(X 0 2+X 1 2)+(483848769569/458600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (286566604320315993/286625000000000000 : ℝ)) (alpha := (483848769569/458600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1070373333/2000000000 : ℝ)*X 2 0+(5217381979/10000000000 : ℝ)*X 2 1+(-1986321789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1875459199/10000000000 : ℝ)*X 0 0+(1043698971/2000000000 : ℝ)*X 0 1+(2716380461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295075607/10000000000 : ℝ)*X 1 0+(-442735577/2500000000 : ℝ)*X 1 1+(2716380833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1059015293/2000000000 : ℝ)*X 2 0+(5432761429/10000000000 : ℝ)*X 2 1+(-354188291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1068043833/2500000000 : ℝ)*X 0 0+(4520162281/10000000000 : ℝ)*X 0 1+(504500799/1250000000 : ℝ)*X 0 2+(1068043833/2500000000 : ℝ)*X 1 0+(4520162281/10000000000 : ℝ)*X 1 1+(504500799/1250000000 : ℝ)*X 1 2+(1068043833/2500000000 : ℝ)*X 2 0+(4520162281/10000000000 : ℝ)*X 2 1+(504500799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1217745711290035721961/917200000000000000000000000 : ℝ) := by norm_num
    linear_combination (1881777649/100000000000000 : ℝ)*(base19) + (3194616607/100000000000000 : ℝ)*(base23) + (568233303/100000000000000 : ℝ)*(lower1) + (638449259/100000000000000 : ℝ)*(upper3) + (27366043/20000000000000 : ℝ)*(lower4) + (13211577/2500000000000 : ℝ)*(upper5) + (673250974072223/20000000000000 : ℝ)*(major0) + (673250974072223/20000000000000 : ℝ)*(major1) + (673250974072223/20000000000000 : ℝ)*(major2) + (13901499027/50000000000000 : ℝ)*(sp0) + (466706805257021/10000000000000 : ℝ)*(sp1) + (4667066170792561/100000000000000 : ℝ)*(sp2) + (93340741099111/2000000000000 : ℝ)*(sp3) + (258180205487011/12500000000000 : ℝ)*(sp4) + (258180205487011/12500000000000 : ℝ)*(f.failure) + (466706805257021/10000000000000 : ℝ)*(f.sum) + (18266272225749/4586000000000000000000000000 : ℝ)*base66 + (75970404044503407/2866250000000000000000000000000 : ℝ)*base67 + (12369145973664093/2866250000000000000000000000000 : ℝ)*base70 + (249111009134197157/2866250000000000000000000000000 : ℝ)*base71 + (23345021938953/4586000000000000000000000000 : ℝ)*base74 + (86001483327111593/2866250000000000000000000000000 : ℝ)*base76 + (16714194736735907/2866250000000000000000000000000 : ℝ)*base77 + (21625065267919093/2866250000000000000000000000000 : ℝ)*base80 + (11399338973153/4586000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4987977/1250000000000000000000 : ℝ)*base89 + (4987977/1250000000000000000000 : ℝ)*base91 + (4987977/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1507_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1507_s7_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875431309/10000000000 : ℝ)*x 0 + (1086775801/2000000000 : ℝ)*x 1 + (5217384063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875431309/10000000000 : ℝ)^4511 ≤ (11471982321567/100000000000000 : ℝ)^3487 := by
    have hnat : (1875431309 : ℕ)^4511*100000000000000^3487 ≤ 11471982321567^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875431309 10000000000 11471982321567 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086775801/2000000000 : ℝ)^4511 ≤ (22713903918489/50000000000000 : ℝ)^3487 := by
    have hnat : (1086775801 : ℕ)^4511*50000000000000^3487 ≤ 22713903918489^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086775801 2000000000 22713903918489 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217384063/10000000000 : ℝ)^4511 ≤ (5387526228123/12500000000000 : ℝ)^3487 := by
    have hnat : (5217384063 : ℕ)^4511*12500000000000^3487 ≤ 5387526228123^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217384063 10000000000 5387526228123 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875431309/10000000000 : ℝ), (1086775801/2000000000 : ℝ), (5217384063/10000000000 : ℝ)] ![(11471982321567/100000000000000 : ℝ), (22713903918489/50000000000000 : ℝ), (5387526228123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875431309/10000000000 : ℝ)|^4511 ≤ (11471982321567/100000000000000 : ℝ)^3487
        have hw : |(-1875431309/10000000000 : ℝ)|=(1875431309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086775801/2000000000 : ℝ)|^4511 ≤ (22713903918489/50000000000000 : ℝ)^3487
        have hw : |(1086775801/2000000000 : ℝ)|=(1086775801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217384063/10000000000 : ℝ)|^4511 ≤ (5387526228123/12500000000000 : ℝ)^3487
        have hw : |(5217384063/10000000000 : ℝ)|=(5217384063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s7_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337966223/2500000000 : ℝ)*x 0 + (-993160347/5000000000 : ℝ)*x 1 + (521738459/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337966223/2500000000 : ℝ)^4511 ≤ (44542785332979/100000000000000 : ℝ)^3487 := by
    have hnat : (1337966223 : ℕ)^4511*100000000000000^3487 ≤ 44542785332979^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337966223 2500000000 44542785332979 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993160347/5000000000 : ℝ)^4511 ≤ (1544624899791/12500000000000 : ℝ)^3487 := by
    have hnat : (993160347 : ℕ)^4511*12500000000000^3487 ≤ 1544624899791^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993160347 5000000000 1544624899791 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521738459/1000000000 : ℝ)^4511 ≤ (1724008618277/4000000000000 : ℝ)^3487 := by
    have hnat : (521738459 : ℕ)^4511*4000000000000^3487 ≤ 1724008618277^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521738459 1000000000 1724008618277 4000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337966223/2500000000 : ℝ), (-993160347/5000000000 : ℝ), (521738459/1000000000 : ℝ)] ![(44542785332979/100000000000000 : ℝ), (1544624899791/12500000000000 : ℝ), (1724008618277/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337966223/2500000000 : ℝ)|^4511 ≤ (44542785332979/100000000000000 : ℝ)^3487
        have hw : |(1337966223/2500000000 : ℝ)|=(1337966223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993160347/5000000000 : ℝ)|^4511 ≤ (1544624899791/12500000000000 : ℝ)^3487
        have hw : |(-993160347/5000000000 : ℝ)|=(993160347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521738459/1000000000 : ℝ)|^4511 ≤ (1724008618277/4000000000000 : ℝ)^3487
        have hw : |(521738459/1000000000 : ℝ)|=(521738459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s7_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668983173/1250000000 : ℝ)*x 0 + (5217384229/10000000000 : ℝ)*x 1 + (-397264103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668983173/1250000000 : ℝ)^4511 ≤ (44542790630323/100000000000000 : ℝ)^3487 := by
    have hnat : (668983173 : ℕ)^4511*100000000000000^3487 ≤ 44542790630323^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668983173 1250000000 44542790630323 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217384229/10000000000 : ℝ)^4511 ≤ (2693763224937/6250000000000 : ℝ)^3487 := by
    have hnat : (5217384229 : ℕ)^4511*6250000000000^3487 ≤ 2693763224937^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217384229 10000000000 2693763224937 6250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397264103/2000000000 : ℝ)^4511 ≤ (12356997757747/100000000000000 : ℝ)^3487 := by
    have hnat : (397264103 : ℕ)^4511*100000000000000^3487 ≤ 12356997757747^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397264103 2000000000 12356997757747 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668983173/1250000000 : ℝ), (5217384229/10000000000 : ℝ), (-397264103/2000000000 : ℝ)] ![(44542790630323/100000000000000 : ℝ), (2693763224937/6250000000000 : ℝ), (12356997757747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668983173/1250000000 : ℝ)|^4511 ≤ (44542790630323/100000000000000 : ℝ)^3487
        have hw : |(668983173/1250000000 : ℝ)|=(668983173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217384229/10000000000 : ℝ)|^4511 ≤ (2693763224937/6250000000000 : ℝ)^3487
        have hw : |(5217384229/10000000000 : ℝ)|=(5217384229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397264103/2000000000 : ℝ)|^4511 ≤ (12356997757747/100000000000000 : ℝ)^3487
        have hw : |(-397264103/2000000000 : ℝ)|=(397264103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s7_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272107263/10000000000 : ℝ)*x 0 + (100837017/250000000 : ℝ)*x 1 + (2261335933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272107263/10000000000 : ℝ)^4511 ≤ (8319854424599/25000000000000 : ℝ)^3487 := by
    have hnat : (4272107263 : ℕ)^4511*25000000000000^3487 ≤ 8319854424599^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272107263 10000000000 8319854424599 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100837017/250000000 : ℝ)^4511 ≤ (3089463773503/10000000000000 : ℝ)^3487 := by
    have hnat : (100837017 : ℕ)^4511*10000000000000^3487 ≤ 3089463773503^3487*250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100837017 250000000 3089463773503 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261335933/5000000000 : ℝ)^4511 ≤ (35825944551693/100000000000000 : ℝ)^3487 := by
    have hnat : (2261335933 : ℕ)^4511*100000000000000^3487 ≤ 35825944551693^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261335933 5000000000 35825944551693 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272107263/10000000000 : ℝ), (100837017/250000000 : ℝ), (2261335933/5000000000 : ℝ)] ![(8319854424599/25000000000000 : ℝ), (3089463773503/10000000000000 : ℝ), (35825944551693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272107263/10000000000 : ℝ)|^4511 ≤ (8319854424599/25000000000000 : ℝ)^3487
        have hw : |(4272107263/10000000000 : ℝ)|=(4272107263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100837017/250000000 : ℝ)|^4511 ≤ (3089463773503/10000000000000 : ℝ)^3487
        have hw : |(100837017/250000000 : ℝ)|=(100837017/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261335933/5000000000 : ℝ)|^4511 ≤ (35825944551693/100000000000000 : ℝ)^3487
        have hw : |(2261335933/5000000000 : ℝ)|=(2261335933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s7_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875459913/10000000000 : ℝ)*x 0 + (5218497881/10000000000 : ℝ)*x 1 + (169773669/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875459913/10000000000 : ℝ)^4511 ≤ (11472208674397/100000000000000 : ℝ)^3487 := by
    have hnat : (1875459913 : ℕ)^4511*100000000000000^3487 ≤ 11472208674397^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875459913 10000000000 11472208674397 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218497881/10000000000 : ℝ)^4511 ≤ (21556056671059/50000000000000 : ℝ)^3487 := by
    have hnat : (5218497881 : ℕ)^4511*50000000000000^3487 ≤ 21556056671059^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218497881 10000000000 21556056671059 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169773669/312500000 : ℝ)^4511 ≤ (22707838980341/50000000000000 : ℝ)^3487 := by
    have hnat : (169773669 : ℕ)^4511*50000000000000^3487 ≤ 22707838980341^3487*312500000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169773669 312500000 22707838980341 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875459913/10000000000 : ℝ), (5218497881/10000000000 : ℝ), (169773669/312500000 : ℝ)] ![(11472208674397/100000000000000 : ℝ), (21556056671059/50000000000000 : ℝ), (22707838980341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875459913/10000000000 : ℝ)|^4511 ≤ (11472208674397/100000000000000 : ℝ)^3487
        have hw : |(-1875459913/10000000000 : ℝ)|=(1875459913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218497881/10000000000 : ℝ)|^4511 ≤ (21556056671059/50000000000000 : ℝ)^3487
        have hw : |(5218497881/10000000000 : ℝ)|=(5218497881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169773669/312500000 : ℝ)|^4511 ≤ (22707838980341/50000000000000 : ℝ)^3487
        have hw : |(169773669/312500000 : ℝ)|=(169773669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s7_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213608593/500000000 : ℝ)*x 0 + (565019667/1250000000 : ℝ)*x 1 + (2018007517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213608593/500000000 : ℝ)^4511 ≤ (8320017169643/25000000000000 : ℝ)^3487 := by
    have hnat : (213608593 : ℕ)^4511*25000000000000^3487 ≤ 8320017169643^3487*500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213608593 500000000 8320017169643 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565019667/1250000000 : ℝ)^4511 ≤ (4475022335213/12500000000000 : ℝ)^3487 := by
    have hnat : (565019667 : ℕ)^4511*12500000000000^3487 ≤ 4475022335213^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565019667 1250000000 4475022335213 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018007517/5000000000 : ℝ)^4511 ≤ (7729938157157/25000000000000 : ℝ)^3487 := by
    have hnat : (2018007517 : ℕ)^4511*25000000000000^3487 ≤ 7729938157157^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018007517 5000000000 7729938157157 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213608593/500000000 : ℝ), (565019667/1250000000 : ℝ), (2018007517/5000000000 : ℝ)] ![(8320017169643/25000000000000 : ℝ), (4475022335213/12500000000000 : ℝ), (7729938157157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213608593/500000000 : ℝ)|^4511 ≤ (8320017169643/25000000000000 : ℝ)^3487
        have hw : |(213608593/500000000 : ℝ)|=(213608593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565019667/1250000000 : ℝ)|^4511 ≤ (4475022335213/12500000000000 : ℝ)^3487
        have hw : |(565019667/1250000000 : ℝ)|=(565019667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018007517/5000000000 : ℝ)|^4511 ≤ (7729938157157/25000000000000 : ℝ)^3487
        have hw : |(2018007517/5000000000 : ℝ)|=(2018007517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10897/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (681/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (681/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (681/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (681/6250 : ℝ) ^ (4509/1024 : ℝ) ≤ (5764725629549901/100000000000000000000 : ℝ) := by
    have hpowers : (681/6250 : ℝ)^4509 ≤ (5764725629549901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (681 : ℕ)^4509*100000000000000000000^1024 ≤ 5764725629549901^1024*6250^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        681 6250 5764725629549901 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (681/6250 : ℝ)) (X := (5764725629549901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (13533045147877341/50000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4509 ≤ (13533045147877341/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4509*50000000000000000000^1024 ≤ 13533045147877341^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 13533045147877341 50000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (13533045147877341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005764725629549901/50000000000000000000 : ℝ) ≤ (312508181991639/312500000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50005764725629549901/50000000000000000000 : ℝ)^1024 ≤ (312508181991639/312500000000000 : ℝ)^4509 := by
      have hnat : (50005764725629549901 : ℕ)^1024*312500000000000^4509 ≤ 312508181991639^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005764725629549901 50000000000000000000 312508181991639 312500000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508181991639/312500000000000 : ℝ)) (X := (50005764725629549901/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032830815925304583/100000000000000000000 : ℝ) ≤ (10000745497692909/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (100032830815925304583/100000000000000000000 : ℝ)^1024 ≤ (10000745497692909/10000000000000000 : ℝ)^4509 := by
      have hnat : (100032830815925304583 : ℕ)^1024*10000000000000000^4509 ≤ 10000745497692909^4509*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032830815925304583 100000000000000000000 10000745497692909 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000745497692909/10000000000000000 : ℝ)) (X := (100032830815925304583/100000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013533045147877341/25000000000000000000 : ℝ) ≤ (1000122917165337/1000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (25013533045147877341/25000000000000000000 : ℝ)^1024 ≤ (1000122917165337/1000000000000000 : ℝ)^4509 := by
      have hnat : (25013533045147877341 : ℕ)^1024*1000000000000000^4509 ≤ 1000122917165337^4509*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013533045147877341 25000000000000000000 1000122917165337 1000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000122917165337/1000000000000000 : ℝ)) (X := (25013533045147877341/25000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5764725629549901/100000000000000000000 : ℝ) ≤ ((716260316232295437/716406250000000000 : ℝ)+2*(483673960461/458500000000000 : ℝ)*(681/6250 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (716260316232295437/716406250000000000 : ℝ)+2*(483673960461/458500000000000 : ℝ)*(681/6250 : ℝ)=(312508181991639/312500000000000 : ℝ) by norm_num, show 1+2*(5764725629549901/100000000000000000000 : ℝ)=(50005764725629549901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13533045147877341/50000000000000000000 : ℝ)+(5764725629549901/100000000000000000000 : ℝ) ≤ ((716260316232295437/716406250000000000 : ℝ)+(483673960461/458500000000000 : ℝ)*((15481/100000 : ℝ)+(681/6250 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (716260316232295437/716406250000000000 : ℝ)+(483673960461/458500000000000 : ℝ)*((15481/100000 : ℝ)+(681/6250 : ℝ))=(10000745497692909/10000000000000000 : ℝ) by norm_num, show 1+(13533045147877341/50000000000000000000 : ℝ)+(5764725629549901/100000000000000000000 : ℝ)=(100032830815925304583/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13533045147877341/50000000000000000000 : ℝ) ≤ ((716260316232295437/716406250000000000 : ℝ)+2*(483673960461/458500000000000 : ℝ)*(15481/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (716260316232295437/716406250000000000 : ℝ)+2*(483673960461/458500000000000 : ℝ)*(15481/100000 : ℝ)=(1000122917165337/1000000000000000 : ℝ) by norm_num, show 1+2*(13533045147877341/50000000000000000000 : ℝ)=(25013533045147877341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (716260316232295437/716406250000000000 : ℝ)*(X 1 0+X 2 0)+(483673960461/458500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (716260316232295437/716406250000000000 : ℝ)) (alpha := (483673960461/458500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (716260316232295437/716406250000000000 : ℝ)*(X 0 1+X 2 1)+(483673960461/458500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (716260316232295437/716406250000000000 : ℝ)) (alpha := (483673960461/458500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (716260316232295437/716406250000000000 : ℝ)*(X 0 2+X 1 2)+(483673960461/458500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (681/6250 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (716260316232295437/716406250000000000 : ℝ)) (alpha := (483673960461/458500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1875431309/10000000000 : ℝ)*X 0 0+(1086775801/2000000000 : ℝ)*X 0 1+(5217384063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337966223/2500000000 : ℝ)*X 1 0+(-993160347/5000000000 : ℝ)*X 1 1+(521738459/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668983173/1250000000 : ℝ)*X 2 0+(5217384229/10000000000 : ℝ)*X 2 1+(-397264103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4272107263/10000000000 : ℝ)*X 0 0+(100837017/250000000 : ℝ)*X 0 1+(2261335933/5000000000 : ℝ)*X 0 2+(4272107263/10000000000 : ℝ)*X 1 0+(100837017/250000000 : ℝ)*X 1 1+(2261335933/5000000000 : ℝ)*X 1 2+(4272107263/10000000000 : ℝ)*X 2 0+(100837017/250000000 : ℝ)*X 2 1+(2261335933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1875459913/10000000000 : ℝ)*X 0 0+(5218497881/10000000000 : ℝ)*X 0 1+(169773669/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((213608593/500000000 : ℝ)*X 0 0+(565019667/1250000000 : ℝ)*X 0 1+(2018007517/5000000000 : ℝ)*X 0 2+(213608593/500000000 : ℝ)*X 1 0+(565019667/1250000000 : ℝ)*X 1 1+(2018007517/5000000000 : ℝ)*X 1 2+(213608593/500000000 : ℝ)*X 2 0+(565019667/1250000000 : ℝ)*X 2 1+(2018007517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62842412076017599619703/22925000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71067739/50000000000000 : ℝ)*(base19) + (13744763/4000000000000 : ℝ)*(base23) + (29856631/25000000000000 : ℝ)*(lower2) + (30887961/50000000000000 : ℝ)*(upper3) + (3476767/2500000000000 : ℝ)*(upper5) + (1665814517301533/50000000000000 : ℝ)*(major0) + (1665814517301533/50000000000000 : ℝ)*(major1) + (1665814517301533/50000000000000 : ℝ)*(major2) + (923810041294989/20000000000000 : ℝ)*(sp0) + (288691353421931/6250000000000 : ℝ)*(sp1) + (4619061453267299/100000000000000 : ℝ)*(sp2) + (204419288480009/10000000000000 : ℝ)*(sp3) + (11590411429/100000000000000 : ℝ)*(sp4) + (164807287/5000000000000 : ℝ)*(sp5) + (204419618094583/10000000000000 : ℝ)*(f.failure) + (2309530898443187/50000000000000 : ℝ)*(f.sum) + (44919829348237/11462500000000000000000000000 : ℝ)*base66 + (580773836729918283/71640625000000000000000000000000 : ℝ)*base68 + (124006592315547773/17910156250000000000000000000000 : ℝ)*base69 + (335229304667105783/71640625000000000000000000000000 : ℝ)*base72 + (52808741696687/11462500000000000000000000000 : ℝ)*base74 + (857118397235550467/71640625000000000000000000000000 : ℝ)*base75 + (758577727598980783/71640625000000000000000000000000 : ℝ)*base78 + (73511866718789287/4477539062500000000000000000000 : ℝ)*base79 + (135864927537051/22925000000000000000000000000 : ℝ)*base81 + (5456219/1000000000000000000000 : ℝ)*base90 + (5456219/1000000000000000000000 : ℝ)*base92 + (5456219/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1507_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10897/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1507_box_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207613271/1250000000 : ℝ)*x 0 + (5403373363/10000000000 : ℝ)*x 1 + (2701686109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207613271/1250000000 : ℝ)^4511 ≤ (9803698453409/100000000000000 : ℝ)^3487 := by
    have hnat : (207613271 : ℕ)^4511*100000000000000^3487 ≤ 9803698453409^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207613271 1250000000 9803698453409 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403373363/10000000000 : ℝ)^4511 ≤ (45098156947833/100000000000000 : ℝ)^3487 := by
    have hnat : (5403373363 : ℕ)^4511*100000000000000^3487 ≤ 45098156947833^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403373363 10000000000 45098156947833 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701686109/5000000000 : ℝ)^4511 ≤ (22549072292469/50000000000000 : ℝ)^3487 := by
    have hnat : (2701686109 : ℕ)^4511*50000000000000^3487 ≤ 22549072292469^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701686109 5000000000 22549072292469 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207613271/1250000000 : ℝ), (5403373363/10000000000 : ℝ), (2701686109/5000000000 : ℝ)] ![(9803698453409/100000000000000 : ℝ), (45098156947833/100000000000000 : ℝ), (22549072292469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207613271/1250000000 : ℝ)|^4511 ≤ (9803698453409/100000000000000 : ℝ)^3487
        have hw : |(-207613271/1250000000 : ℝ)|=(207613271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403373363/10000000000 : ℝ)|^4511 ≤ (45098156947833/100000000000000 : ℝ)^3487
        have hw : |(5403373363/10000000000 : ℝ)|=(5403373363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701686109/5000000000 : ℝ)|^4511 ≤ (22549072292469/50000000000000 : ℝ)^3487
        have hw : |(2701686109/5000000000 : ℝ)|=(2701686109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270710709/10000000000 : ℝ)*x 0 + (-115305831/625000000 : ℝ)*x 1 + (2701685919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270710709/10000000000 : ℝ)^4511 ≤ (43670953947093/100000000000000 : ℝ)^3487 := by
    have hnat : (5270710709 : ℕ)^4511*100000000000000^3487 ≤ 43670953947093^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270710709 10000000000 43670953947093 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115305831/625000000 : ℝ)^4511 ≤ (11230905556471/100000000000000 : ℝ)^3487 := by
    have hnat : (115305831 : ℕ)^4511*100000000000000^3487 ≤ 11230905556471^3487*625000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115305831 625000000 11230905556471 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701685919/5000000000 : ℝ)^4511 ≤ (45098140481969/100000000000000 : ℝ)^3487 := by
    have hnat : (2701685919 : ℕ)^4511*100000000000000^3487 ≤ 45098140481969^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701685919 5000000000 45098140481969 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270710709/10000000000 : ℝ), (-115305831/625000000 : ℝ), (2701685919/5000000000 : ℝ)] ![(43670953947093/100000000000000 : ℝ), (11230905556471/100000000000000 : ℝ), (45098140481969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270710709/10000000000 : ℝ)|^4511 ≤ (43670953947093/100000000000000 : ℝ)^3487
        have hw : |(5270710709/10000000000 : ℝ)|=(5270710709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115305831/625000000 : ℝ)|^4511 ≤ (11230905556471/100000000000000 : ℝ)^3487
        have hw : |(-115305831/625000000 : ℝ)|=(115305831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701685919/5000000000 : ℝ)|^4511 ≤ (45098140481969/100000000000000 : ℝ)^3487
        have hw : |(2701685919/5000000000 : ℝ)|=(2701685919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635356123/5000000000 : ℝ)*x 0 + (5403371137/10000000000 : ℝ)*x 1 + (-368978433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635356123/5000000000 : ℝ)^4511 ≤ (21835485210911/50000000000000 : ℝ)^3487 := by
    have hnat : (2635356123 : ℕ)^4511*50000000000000^3487 ≤ 21835485210911^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635356123 5000000000 21835485210911 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403371137/10000000000 : ℝ)^4511 ≤ (45098132913071/100000000000000 : ℝ)^3487 := by
    have hnat : (5403371137 : ℕ)^4511*100000000000000^3487 ≤ 45098132913071^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403371137 10000000000 45098132913071 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368978433/2000000000 : ℝ)^4511 ≤ (11230896649563/100000000000000 : ℝ)^3487 := by
    have hnat : (368978433 : ℕ)^4511*100000000000000^3487 ≤ 11230896649563^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368978433 2000000000 11230896649563 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635356123/5000000000 : ℝ), (5403371137/10000000000 : ℝ), (-368978433/2000000000 : ℝ)] ![(21835485210911/50000000000000 : ℝ), (45098132913071/100000000000000 : ℝ), (11230896649563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635356123/5000000000 : ℝ)|^4511 ≤ (21835485210911/50000000000000 : ℝ)^3487
        have hw : |(2635356123/5000000000 : ℝ)|=(2635356123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403371137/10000000000 : ℝ)|^4511 ≤ (45098132913071/100000000000000 : ℝ)^3487
        have hw : |(5403371137/10000000000 : ℝ)|=(5403371137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-368978433/2000000000 : ℝ)|^4511 ≤ (11230896649563/100000000000000 : ℝ)^3487
        have hw : |(-368978433/2000000000 : ℝ)|=(368978433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1118849519/2500000000 : ℝ)*x 0 + (1044368501/2500000000 : ℝ)*x 1 + (2088738163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118849519/2500000000 : ℝ)^4511 ≤ (35342245577023/100000000000000 : ℝ)^3487 := by
    have hnat : (1118849519 : ℕ)^4511*100000000000000^3487 ≤ 35342245577023^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118849519 2500000000 35342245577023 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044368501/2500000000 : ℝ)^4511 ≤ (32328865583981/100000000000000 : ℝ)^3487 := by
    have hnat : (1044368501 : ℕ)^4511*100000000000000^3487 ≤ 32328865583981^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044368501 2500000000 32328865583981 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088738163/5000000000 : ℝ)^4511 ≤ (32328888830603/100000000000000 : ℝ)^3487 := by
    have hnat : (2088738163 : ℕ)^4511*100000000000000^3487 ≤ 32328888830603^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088738163 5000000000 32328888830603 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118849519/2500000000 : ℝ), (1044368501/2500000000 : ℝ), (2088738163/5000000000 : ℝ)] ![(35342245577023/100000000000000 : ℝ), (32328865583981/100000000000000 : ℝ), (32328888830603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118849519/2500000000 : ℝ)|^4511 ≤ (35342245577023/100000000000000 : ℝ)^3487
        have hw : |(1118849519/2500000000 : ℝ)|=(1118849519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044368501/2500000000 : ℝ)|^4511 ≤ (32328865583981/100000000000000 : ℝ)^3487
        have hw : |(1044368501/2500000000 : ℝ)|=(1044368501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2088738163/5000000000 : ℝ)|^4511 ≤ (32328888830603/100000000000000 : ℝ)^3487
        have hw : |(2088738163/5000000000 : ℝ)|=(2088738163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-523848843/2500000000 : ℝ)*x 0 + (1048692261/2000000000 : ℝ)*x 1 + (524346073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523848843/2500000000 : ℝ)^4511 ≤ (3310453419457/25000000000000 : ℝ)^3487 := by
    have hnat : (523848843 : ℕ)^4511*25000000000000^3487 ≤ 3310453419457^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523848843 2500000000 3310453419457 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048692261/2000000000 : ℝ)^4511 ≤ (43379096230411/100000000000000 : ℝ)^3487 := by
    have hnat : (1048692261 : ℕ)^4511*100000000000000^3487 ≤ 43379096230411^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048692261 2000000000 43379096230411 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524346073/1000000000 : ℝ)^4511 ≤ (43379090076501/100000000000000 : ℝ)^3487 := by
    have hnat : (524346073 : ℕ)^4511*100000000000000^3487 ≤ 43379090076501^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524346073 1000000000 43379090076501 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523848843/2500000000 : ℝ), (1048692261/2000000000 : ℝ), (524346073/1000000000 : ℝ)] ![(3310453419457/25000000000000 : ℝ), (43379096230411/100000000000000 : ℝ), (43379090076501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523848843/2500000000 : ℝ)|^4511 ≤ (3310453419457/25000000000000 : ℝ)^3487
        have hw : |(-523848843/2500000000 : ℝ)|=(523848843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048692261/2000000000 : ℝ)|^4511 ≤ (43379096230411/100000000000000 : ℝ)^3487
        have hw : |(1048692261/2000000000 : ℝ)|=(1048692261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524346073/1000000000 : ℝ)|^4511 ≤ (43379090076501/100000000000000 : ℝ)^3487
        have hw : |(524346073/1000000000 : ℝ)|=(524346073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538208779/1000000000 : ℝ)*x 0 + (-238847013/1250000000 : ℝ)*x 1 + (5243460651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538208779/1000000000 : ℝ)^4511 ≤ (44868463538697/100000000000000 : ℝ)^3487 := by
    have hnat : (538208779 : ℕ)^4511*100000000000000^3487 ≤ 44868463538697^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538208779 1000000000 44868463538697 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238847013/1250000000 : ℝ)^4511 ≤ (1469055901551/12500000000000 : ℝ)^3487 := by
    have hnat : (238847013 : ℕ)^4511*12500000000000^3487 ≤ 1469055901551^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238847013 1250000000 1469055901551 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243460651/10000000000 : ℝ)^4511 ≤ (43379089231007/100000000000000 : ℝ)^3487 := by
    have hnat : (5243460651 : ℕ)^4511*100000000000000^3487 ≤ 43379089231007^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243460651 10000000000 43379089231007 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538208779/1000000000 : ℝ), (-238847013/1250000000 : ℝ), (5243460651/10000000000 : ℝ)] ![(44868463538697/100000000000000 : ℝ), (1469055901551/12500000000000 : ℝ), (43379089231007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538208779/1000000000 : ℝ)|^4511 ≤ (44868463538697/100000000000000 : ℝ)^3487
        have hw : |(538208779/1000000000 : ℝ)|=(538208779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238847013/1250000000 : ℝ)|^4511 ≤ (1469055901551/12500000000000 : ℝ)^3487
        have hw : |(-238847013/1250000000 : ℝ)|=(238847013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243460651/10000000000 : ℝ)|^4511 ≤ (43379089231007/100000000000000 : ℝ)^3487
        have hw : |(5243460651/10000000000 : ℝ)|=(5243460651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336380467/625000000 : ℝ)*x 0 + (1310865117/2500000000 : ℝ)*x 1 + (-1910776783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336380467/625000000 : ℝ)^4511 ≤ (44868460109137/100000000000000 : ℝ)^3487 := by
    have hnat : (336380467 : ℕ)^4511*100000000000000^3487 ≤ 44868460109137^3487*625000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336380467 625000000 44868460109137 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310865117/2500000000 : ℝ)^4511 ≤ (21689543636229/50000000000000 : ℝ)^3487 := by
    have hnat : (1310865117 : ℕ)^4511*50000000000000^3487 ≤ 21689543636229^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310865117 2500000000 21689543636229 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1910776783/10000000000 : ℝ)^4511 ≤ (11752452615087/100000000000000 : ℝ)^3487 := by
    have hnat : (1910776783 : ℕ)^4511*100000000000000^3487 ≤ 11752452615087^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910776783 10000000000 11752452615087 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336380467/625000000 : ℝ), (1310865117/2500000000 : ℝ), (-1910776783/10000000000 : ℝ)] ![(44868460109137/100000000000000 : ℝ), (21689543636229/50000000000000 : ℝ), (11752452615087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336380467/625000000 : ℝ)|^4511 ≤ (44868460109137/100000000000000 : ℝ)^3487
        have hw : |(336380467/625000000 : ℝ)|=(336380467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310865117/2500000000 : ℝ)|^4511 ≤ (21689543636229/50000000000000 : ℝ)^3487
        have hw : |(1310865117/2500000000 : ℝ)|=(1310865117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1910776783/10000000000 : ℝ)|^4511 ≤ (11752452615087/100000000000000 : ℝ)^3487
        have hw : |(-1910776783/10000000000 : ℝ)|=(1910776783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1016605649/2500000000 : ℝ)*x 0 + (2190914297/5000000000 : ℝ)*x 1 + (273864211/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016605649/2500000000 : ℝ)^4511 ≤ (487835085771/1562500000000 : ℝ)^3487 := by
    have hnat : (1016605649 : ℕ)^4511*1562500000000^3487 ≤ 487835085771^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016605649 2500000000 487835085771 1562500000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190914297/5000000000 : ℝ)^4511 ≤ (34389283426519/100000000000000 : ℝ)^3487 := by
    have hnat : (2190914297 : ℕ)^4511*100000000000000^3487 ≤ 34389283426519^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190914297 5000000000 34389283426519 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273864211/625000000 : ℝ)^4511 ≤ (3438927106033/10000000000000 : ℝ)^3487 := by
    have hnat : (273864211 : ℕ)^4511*10000000000000^3487 ≤ 3438927106033^3487*625000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273864211 625000000 3438927106033 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1016605649/2500000000 : ℝ), (2190914297/5000000000 : ℝ), (273864211/625000000 : ℝ)] ![(487835085771/1562500000000 : ℝ), (34389283426519/100000000000000 : ℝ), (3438927106033/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1016605649/2500000000 : ℝ)|^4511 ≤ (487835085771/1562500000000 : ℝ)^3487
        have hw : |(1016605649/2500000000 : ℝ)|=(1016605649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2190914297/5000000000 : ℝ)|^4511 ≤ (34389283426519/100000000000000 : ℝ)^3487
        have hw : |(2190914297/5000000000 : ℝ)|=(2190914297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273864211/625000000 : ℝ)|^4511 ≤ (3438927106033/10000000000000 : ℝ)^3487
        have hw : |(273864211/625000000 : ℝ)|=(273864211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_8 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-500900987/2500000000 : ℝ)*x 0 + (5131485737/10000000000 : ℝ)*x 1 + (216953619/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (500900987/2500000000 : ℝ)^4511 ≤ (781016941873/6250000000000 : ℝ)^3487 := by
    have hnat : (500900987 : ℕ)^4511*6250000000000^3487 ≤ 781016941873^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500900987 2500000000 781016941873 6250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131485737/10000000000 : ℝ)^4511 ≤ (21092229929809/50000000000000 : ℝ)^3487 := by
    have hnat : (5131485737 : ℕ)^4511*50000000000000^3487 ≤ 21092229929809^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131485737 10000000000 21092229929809 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216953619/400000000 : ℝ)^4511 ≤ (22659634527307/50000000000000 : ℝ)^3487 := by
    have hnat : (216953619 : ℕ)^4511*50000000000000^3487 ≤ 22659634527307^3487*400000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216953619 400000000 22659634527307 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-500900987/2500000000 : ℝ), (5131485737/10000000000 : ℝ), (216953619/400000000 : ℝ)] ![(781016941873/6250000000000 : ℝ), (21092229929809/50000000000000 : ℝ), (22659634527307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-500900987/2500000000 : ℝ)|^4511 ≤ (781016941873/6250000000000 : ℝ)^3487
        have hw : |(-500900987/2500000000 : ℝ)|=(500900987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131485737/10000000000 : ℝ)|^4511 ≤ (21092229929809/50000000000000 : ℝ)^3487
        have hw : |(5131485737/10000000000 : ℝ)|=(5131485737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216953619/400000000 : ℝ)|^4511 ≤ (22659634527307/50000000000000 : ℝ)^3487
        have hw : |(216953619/400000000 : ℝ)|=(216953619/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_9 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628224301/5000000000 : ℝ)*x 0 + (-918106199/5000000000 : ℝ)*x 1 + (5423840443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628224301/5000000000 : ℝ)^4511 ≤ (21759071340547/50000000000000 : ℝ)^3487 := by
    have hnat : (2628224301 : ℕ)^4511*50000000000000^3487 ≤ 21759071340547^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628224301 5000000000 21759071340547 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918106199/5000000000 : ℝ)^4511 ≤ (5581294295533/50000000000000 : ℝ)^3487 := by
    have hnat : (918106199 : ℕ)^4511*50000000000000^3487 ≤ 5581294295533^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918106199 5000000000 5581294295533 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423840443/10000000000 : ℝ)^4511 ≤ (45319268708717/100000000000000 : ℝ)^3487 := by
    have hnat : (5423840443 : ℕ)^4511*100000000000000^3487 ≤ 45319268708717^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423840443 10000000000 45319268708717 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628224301/5000000000 : ℝ), (-918106199/5000000000 : ℝ), (5423840443/10000000000 : ℝ)] ![(21759071340547/50000000000000 : ℝ), (5581294295533/50000000000000 : ℝ), (45319268708717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628224301/5000000000 : ℝ)|^4511 ≤ (21759071340547/50000000000000 : ℝ)^3487
        have hw : |(2628224301/5000000000 : ℝ)|=(2628224301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-918106199/5000000000 : ℝ)|^4511 ≤ (5581294295533/50000000000000 : ℝ)^3487
        have hw : |(-918106199/5000000000 : ℝ)|=(918106199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423840443/10000000000 : ℝ)|^4511 ≤ (45319268708717/100000000000000 : ℝ)^3487
        have hw : |(5423840443/10000000000 : ℝ)|=(5423840443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_10 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8213201/15625000 : ℝ)*x 0 + (1355960171/2500000000 : ℝ)*x 1 + (-367242403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8213201/15625000 : ℝ)^4511 ≤ (21759071544041/50000000000000 : ℝ)^3487 := by
    have hnat : (8213201 : ℕ)^4511*50000000000000^3487 ≤ 21759071544041^3487*15625000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8213201 15625000 21759071544041 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355960171/2500000000 : ℝ)^4511 ≤ (22659635656877/50000000000000 : ℝ)^3487 := by
    have hnat : (1355960171 : ℕ)^4511*50000000000000^3487 ≤ 22659635656877^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355960171 2500000000 22659635656877 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367242403/2000000000 : ℝ)^4511 ≤ (558129278951/5000000000000 : ℝ)^3487 := by
    have hnat : (367242403 : ℕ)^4511*5000000000000^3487 ≤ 558129278951^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367242403 2000000000 558129278951 5000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8213201/15625000 : ℝ), (1355960171/2500000000 : ℝ), (-367242403/2000000000 : ℝ)] ![(21759071544041/50000000000000 : ℝ), (22659635656877/50000000000000 : ℝ), (558129278951/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8213201/15625000 : ℝ)|^4511 ≤ (21759071544041/50000000000000 : ℝ)^3487
        have hw : |(8213201/15625000 : ℝ)|=(8213201/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355960171/2500000000 : ℝ)|^4511 ≤ (22659635656877/50000000000000 : ℝ)^3487
        have hw : |(1355960171/2500000000 : ℝ)|=(1355960171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367242403/2000000000 : ℝ)|^4511 ≤ (558129278951/5000000000000 : ℝ)^3487
        have hw : |(-367242403/2000000000 : ℝ)|=(367242403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_11 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4526590743/10000000000 : ℝ)*x 0 + (518910997/1250000000 : ℝ)*x 1 + (518910967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4526590743/10000000000 : ℝ)^4511 ≤ (35866108862783/100000000000000 : ℝ)^3487 := by
    have hnat : (4526590743 : ℕ)^4511*100000000000000^3487 ≤ 35866108862783^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526590743 10000000000 35866108862783 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518910997/1250000000 : ℝ)^4511 ≤ (32066946755881/100000000000000 : ℝ)^3487 := by
    have hnat : (518910997 : ℕ)^4511*100000000000000^3487 ≤ 32066946755881^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518910997 1250000000 32066946755881 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518910967/1250000000 : ℝ)^4511 ≤ (16033472178781/50000000000000 : ℝ)^3487 := by
    have hnat : (518910967 : ℕ)^4511*50000000000000^3487 ≤ 16033472178781^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518910967 1250000000 16033472178781 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4526590743/10000000000 : ℝ), (518910997/1250000000 : ℝ), (518910967/1250000000 : ℝ)] ![(35866108862783/100000000000000 : ℝ), (32066946755881/100000000000000 : ℝ), (16033472178781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4526590743/10000000000 : ℝ)|^4511 ≤ (35866108862783/100000000000000 : ℝ)^3487
        have hw : |(4526590743/10000000000 : ℝ)|=(4526590743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518910997/1250000000 : ℝ)|^4511 ≤ (32066946755881/100000000000000 : ℝ)^3487
        have hw : |(518910997/1250000000 : ℝ)|=(518910997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518910967/1250000000 : ℝ)|^4511 ≤ (16033472178781/50000000000000 : ℝ)^3487
        have hw : |(518910967/1250000000 : ℝ)|=(518910967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_12 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87633721/500000000 : ℝ)*x 0 + (2755865759/5000000000 : ℝ)*x 1 + (2614219423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87633721/500000000 : ℝ)^4511 ≤ (10510053161851/100000000000000 : ℝ)^3487 := by
    have hnat : (87633721 : ℕ)^4511*100000000000000^3487 ≤ 10510053161851^3487*500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87633721 500000000 10510053161851 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755865759/5000000000 : ℝ)^4511 ≤ (5783945008433/12500000000000 : ℝ)^3487 := by
    have hnat : (2755865759 : ℕ)^4511*12500000000000^3487 ≤ 5783945008433^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755865759 5000000000 5783945008433 12500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614219423/5000000000 : ℝ)^4511 ≤ (21609193377587/50000000000000 : ℝ)^3487 := by
    have hnat : (2614219423 : ℕ)^4511*50000000000000^3487 ≤ 21609193377587^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614219423 5000000000 21609193377587 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87633721/500000000 : ℝ), (2755865759/5000000000 : ℝ), (2614219423/5000000000 : ℝ)] ![(10510053161851/100000000000000 : ℝ), (5783945008433/12500000000000 : ℝ), (21609193377587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87633721/500000000 : ℝ)|^4511 ≤ (10510053161851/100000000000000 : ℝ)^3487
        have hw : |(-87633721/500000000 : ℝ)|=(87633721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755865759/5000000000 : ℝ)|^4511 ≤ (5783945008433/12500000000000 : ℝ)^3487
        have hw : |(2755865759/5000000000 : ℝ)|=(2755865759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614219423/5000000000 : ℝ)|^4511 ≤ (21609193377587/50000000000000 : ℝ)^3487
        have hw : |(2614219423/5000000000 : ℝ)|=(2614219423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_13 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392550129/10000000000 : ℝ)*x 0 + (-1916785449/10000000000 : ℝ)*x 1 + (5228438747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392550129/10000000000 : ℝ)^4511 ≤ (22490664878443/50000000000000 : ℝ)^3487 := by
    have hnat : (5392550129 : ℕ)^4511*50000000000000^3487 ≤ 22490664878443^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392550129 10000000000 22490664878443 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916785449/10000000000 : ℝ)^4511 ≤ (11800284536629/100000000000000 : ℝ)^3487 := by
    have hnat : (1916785449 : ℕ)^4511*100000000000000^3487 ≤ 11800284536629^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916785449 10000000000 11800284536629 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228438747/10000000000 : ℝ)^4511 ≤ (10804596424131/25000000000000 : ℝ)^3487 := by
    have hnat : (5228438747 : ℕ)^4511*25000000000000^3487 ≤ 10804596424131^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228438747 10000000000 10804596424131 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392550129/10000000000 : ℝ), (-1916785449/10000000000 : ℝ), (5228438747/10000000000 : ℝ)] ![(22490664878443/50000000000000 : ℝ), (11800284536629/100000000000000 : ℝ), (10804596424131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392550129/10000000000 : ℝ)|^4511 ≤ (22490664878443/50000000000000 : ℝ)^3487
        have hw : |(5392550129/10000000000 : ℝ)|=(5392550129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916785449/10000000000 : ℝ)|^4511 ≤ (11800284536629/100000000000000 : ℝ)^3487
        have hw : |(-1916785449/10000000000 : ℝ)|=(1916785449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228438747/10000000000 : ℝ)|^4511 ≤ (10804596424131/25000000000000 : ℝ)^3487
        have hw : |(5228438747/10000000000 : ℝ)|=(5228438747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_14 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392549887/10000000000 : ℝ)*x 0 + (2614219397/5000000000 : ℝ)*x 1 + (-1916785713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392549887/10000000000 : ℝ)^4511 ≤ (1124533178637/2500000000000 : ℝ)^3487 := by
    have hnat : (5392549887 : ℕ)^4511*2500000000000^3487 ≤ 1124533178637^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392549887 10000000000 1124533178637 2500000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614219397/5000000000 : ℝ)^4511 ≤ (8643677239823/20000000000000 : ℝ)^3487 := by
    have hnat : (2614219397 : ℕ)^4511*20000000000000^3487 ≤ 8643677239823^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614219397 5000000000 8643677239823 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916785713/10000000000 : ℝ)^4511 ≤ (11800286639167/100000000000000 : ℝ)^3487 := by
    have hnat : (1916785713 : ℕ)^4511*100000000000000^3487 ≤ 11800286639167^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916785713 10000000000 11800286639167 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392549887/10000000000 : ℝ), (2614219397/5000000000 : ℝ), (-1916785713/10000000000 : ℝ)] ![(1124533178637/2500000000000 : ℝ), (8643677239823/20000000000000 : ℝ), (11800286639167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392549887/10000000000 : ℝ)|^4511 ≤ (1124533178637/2500000000000 : ℝ)^3487
        have hw : |(5392549887/10000000000 : ℝ)|=(5392549887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614219397/5000000000 : ℝ)|^4511 ≤ (8643677239823/20000000000000 : ℝ)^3487
        have hw : |(2614219397/5000000000 : ℝ)|=(2614219397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916785713/10000000000 : ℝ)|^4511 ≤ (11800286639167/100000000000000 : ℝ)^3487
        have hw : |(-1916785713/10000000000 : ℝ)|=(1916785713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_box_15 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (503392751/1250000000 : ℝ)*x 0 + (880200477/2000000000 : ℝ)*x 1 + (1100250651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503392751/1250000000 : ℝ)^4511 ≤ (30831843174651/100000000000000 : ℝ)^3487 := by
    have hnat : (503392751 : ℕ)^4511*100000000000000^3487 ≤ 30831843174651^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503392751 1250000000 30831843174651 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880200477/2000000000 : ℝ)^4511 ≤ (1383363091513/4000000000000 : ℝ)^3487 := by
    have hnat : (880200477 : ℕ)^4511*4000000000000^3487 ≤ 1383363091513^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880200477 2000000000 1383363091513 4000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100250651/2500000000 : ℝ)^4511 ≤ (6916815902831/20000000000000 : ℝ)^3487 := by
    have hnat : (1100250651 : ℕ)^4511*20000000000000^3487 ≤ 6916815902831^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100250651 2500000000 6916815902831 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503392751/1250000000 : ℝ), (880200477/2000000000 : ℝ), (1100250651/2500000000 : ℝ)] ![(30831843174651/100000000000000 : ℝ), (1383363091513/4000000000000 : ℝ), (6916815902831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503392751/1250000000 : ℝ)|^4511 ≤ (30831843174651/100000000000000 : ℝ)^3487
        have hw : |(503392751/1250000000 : ℝ)|=(503392751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880200477/2000000000 : ℝ)|^4511 ≤ (1383363091513/4000000000000 : ℝ)^3487
        have hw : |(880200477/2000000000 : ℝ)|=(880200477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100250651/2500000000 : ℝ)|^4511 ≤ (6916815902831/20000000000000 : ℝ)^3487
        have hw : |(1100250651/2500000000 : ℝ)|=(1100250651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63733/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14651/25000 : ℝ) ∧ (16053/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8597/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10897/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (2883527824780233/50000000000000000000 : ℝ) := by
    have hpowers : (10897/100000 : ℝ)^4509 ≤ (2883527824780233/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10897 : ℕ)^4509*50000000000000000000^1024 ≤ 2883527824780233^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10897 100000 2883527824780233 50000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10897/100000 : ℝ)) (X := (2883527824780233/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (13533045147877341/50000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4509 ≤ (13533045147877341/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4509*50000000000000000000^1024 ≤ 13533045147877341^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 13533045147877341 50000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (13533045147877341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002883527824780233/25000000000000000000 : ℝ) ≤ (2000052385910631/2000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (25002883527824780233/25000000000000000000 : ℝ)^1024 ≤ (2000052385910631/2000000000000000 : ℝ)^4509 := by
      have hnat : (25002883527824780233 : ℕ)^1024*2000000000000000^4509 ≤ 2000052385910631^4509*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002883527824780233 25000000000000000000 2000052385910631 2000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000052385910631/2000000000000000 : ℝ)) (X := (25002883527824780233/25000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008208286486328787/25000000000000000000 : ℝ) ≤ (2000149110118911/2000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (25008208286486328787/25000000000000000000 : ℝ)^1024 ≤ (2000149110118911/2000000000000000 : ℝ)^4509 := by
      have hnat : (25008208286486328787 : ℕ)^1024*2000000000000000^4509 ≤ 2000149110118911^4509*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008208286486328787 25000000000000000000 2000149110118911 2000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000149110118911/2000000000000000 : ℝ)) (X := (25008208286486328787/25000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013533045147877341/25000000000000000000 : ℝ) ≤ (2000245834327191/2000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (25013533045147877341/25000000000000000000 : ℝ)^1024 ≤ (2000245834327191/2000000000000000 : ℝ)^4509 := by
      have hnat : (25013533045147877341 : ℕ)^1024*2000000000000000^4509 ≤ 2000245834327191^4509*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013533045147877341 25000000000000000000 2000245834327191 2000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000245834327191/2000000000000000 : ℝ)) (X := (25013533045147877341/25000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2883527824780233/50000000000000000000 : ℝ) ≤ ((381922172067461591/382000000000000000 : ℝ)+2*(806035069/764000000000 : ℝ)*(10897/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (381922172067461591/382000000000000000 : ℝ)+2*(806035069/764000000000 : ℝ)*(10897/100000 : ℝ)=(2000052385910631/2000000000000000 : ℝ) by norm_num, show 1+2*(2883527824780233/50000000000000000000 : ℝ)=(25002883527824780233/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13533045147877341/50000000000000000000 : ℝ)+(2883527824780233/50000000000000000000 : ℝ) ≤ ((381922172067461591/382000000000000000 : ℝ)+(806035069/764000000000 : ℝ)*((15481/100000 : ℝ)+(10897/100000 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (381922172067461591/382000000000000000 : ℝ)+(806035069/764000000000 : ℝ)*((15481/100000 : ℝ)+(10897/100000 : ℝ))=(2000149110118911/2000000000000000 : ℝ) by norm_num, show 1+(13533045147877341/50000000000000000000 : ℝ)+(2883527824780233/50000000000000000000 : ℝ)=(25008208286486328787/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13533045147877341/50000000000000000000 : ℝ) ≤ ((381922172067461591/382000000000000000 : ℝ)+2*(806035069/764000000000 : ℝ)*(15481/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (381922172067461591/382000000000000000 : ℝ)+2*(806035069/764000000000 : ℝ)*(15481/100000 : ℝ)=(2000245834327191/2000000000000000 : ℝ) by norm_num, show 1+2*(13533045147877341/50000000000000000000 : ℝ)=(25013533045147877341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (381922172067461591/382000000000000000 : ℝ)*(X 1 0+X 2 0)+(806035069/764000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (10897/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (381922172067461591/382000000000000000 : ℝ)) (alpha := (806035069/764000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (381922172067461591/382000000000000000 : ℝ)*(X 0 1+X 2 1)+(806035069/764000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (10897/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (381922172067461591/382000000000000000 : ℝ)) (alpha := (806035069/764000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (381922172067461591/382000000000000000 : ℝ)*(X 0 2+X 1 2)+(806035069/764000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (10897/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (381922172067461591/382000000000000000 : ℝ)) (alpha := (806035069/764000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207613271/1250000000 : ℝ)*X 0 0+(5403373363/10000000000 : ℝ)*X 0 1+(2701686109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270710709/10000000000 : ℝ)*X 1 0+(-115305831/625000000 : ℝ)*X 1 1+(2701685919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635356123/5000000000 : ℝ)*X 2 0+(5403371137/10000000000 : ℝ)*X 2 1+(-368978433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1118849519/2500000000 : ℝ)*X 0 0+(1044368501/2500000000 : ℝ)*X 0 1+(2088738163/5000000000 : ℝ)*X 0 2+(1118849519/2500000000 : ℝ)*X 1 0+(1044368501/2500000000 : ℝ)*X 1 1+(2088738163/5000000000 : ℝ)*X 1 2+(1118849519/2500000000 : ℝ)*X 2 0+(1044368501/2500000000 : ℝ)*X 2 1+(2088738163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-523848843/2500000000 : ℝ)*X 0 0+(1048692261/2000000000 : ℝ)*X 0 1+(524346073/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538208779/1000000000 : ℝ)*X 1 0+(-238847013/1250000000 : ℝ)*X 1 1+(5243460651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((336380467/625000000 : ℝ)*X 2 0+(1310865117/2500000000 : ℝ)*X 2 1+(-1910776783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1016605649/2500000000 : ℝ)*X 0 0+(2190914297/5000000000 : ℝ)*X 0 1+(273864211/625000000 : ℝ)*X 0 2+(1016605649/2500000000 : ℝ)*X 1 0+(2190914297/5000000000 : ℝ)*X 1 1+(273864211/625000000 : ℝ)*X 1 2+(1016605649/2500000000 : ℝ)*X 2 0+(2190914297/5000000000 : ℝ)*X 2 1+(273864211/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-500900987/2500000000 : ℝ)*X 0 0+(5131485737/10000000000 : ℝ)*X 0 1+(216953619/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628224301/5000000000 : ℝ)*X 1 0+(-918106199/5000000000 : ℝ)*X 1 1+(5423840443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((8213201/15625000 : ℝ)*X 2 0+(1355960171/2500000000 : ℝ)*X 2 1+(-367242403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4526590743/10000000000 : ℝ)*X 0 0+(518910997/1250000000 : ℝ)*X 0 1+(518910967/1250000000 : ℝ)*X 0 2+(4526590743/10000000000 : ℝ)*X 1 0+(518910997/1250000000 : ℝ)*X 1 1+(518910967/1250000000 : ℝ)*X 1 2+(4526590743/10000000000 : ℝ)*X 2 0+(518910997/1250000000 : ℝ)*X 2 1+(518910967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-87633721/500000000 : ℝ)*X 0 0+(2755865759/5000000000 : ℝ)*X 0 1+(2614219423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392550129/10000000000 : ℝ)*X 1 0+(-1916785449/10000000000 : ℝ)*X 1 1+(5228438747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392549887/10000000000 : ℝ)*X 2 0+(2614219397/5000000000 : ℝ)*X 2 1+(-1916785713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((503392751/1250000000 : ℝ)*X 0 0+(880200477/2000000000 : ℝ)*X 0 1+(1100250651/2500000000 : ℝ)*X 0 2+(503392751/1250000000 : ℝ)*X 1 0+(880200477/2000000000 : ℝ)*X 1 1+(1100250651/2500000000 : ℝ)*X 1 2+(503392751/1250000000 : ℝ)*X 2 0+(880200477/2000000000 : ℝ)*X 2 1+(1100250651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63733/100000 : ℝ) ≤ (-380390425084854660453320288889/596875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19680771/25000000000000 : ℝ)*(upper1) + (10186541/50000000000000 : ℝ)*(upper2) + (285535047/100000000000000 : ℝ)*(upper3) + (12160487/12500000000000 : ℝ)*(lower4) + (69251271435093/3125000000000 : ℝ)*(major0) + (69251271435093/3125000000000 : ℝ)*(major1) + (69251271435093/3125000000000 : ℝ)*(major2) + (14461250991/100000000000000 : ℝ)*(sp1) + (8096278079/50000000000000 : ℝ)*(sp2) + (1824723849/50000000000000 : ℝ)*(sp3) + (1546811521340823/50000000000000 : ℝ)*(sp4) + (618721716286131/20000000000000 : ℝ)*(sp5) + (193350428132843/6250000000000 : ℝ)*(sp6) + (679849062024717/50000000000000 : ℝ)*(sp7) + (339925443374283/25000000000000 : ℝ)*(f.failure) + (1546811521340823/50000000000000 : ℝ)*(f.sum) + (4895024417/4775000000000000000000000 : ℝ)*base66 + (8575950785275463/1193750000000000000000000000000 : ℝ)*base67 + (9759449586937037/1193750000000000000000000000000 : ℝ)*base70 + (22395461021805787/1193750000000000000000000000000 : ℝ)*base72 + (121259823123/47750000000000000000000000 : ℝ)*base74 + (36672786162731713/1193750000000000000000000000000 : ℝ)*base75 + (8882899367037963/1193750000000000000000000000000 : ℝ)*base77 + (6998634585275463/1193750000000000000000000000000 : ℝ)*base79 + (1917879307571/95500000000000000000000000 : ℝ)*base81 + (9531681/2500000000000000000000 : ℝ)*base89 + (9531681/2500000000000000000000 : ℝ)*base91 + (9531681/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14651/25000 : ℝ) ≤ (2798465767145189291829969262383/4775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60024189/100000000000000 : ℝ)*(upper0) + (277849447/50000000000000 : ℝ)*(lower1) + (74627809/12500000000000 : ℝ)*(upper4) + (572984324869857/25000000000000 : ℝ)*(major0) + (572984324869857/25000000000000 : ℝ)*(major1) + (572984324869857/25000000000000 : ℝ)*(major2) + (1579032423460963/50000000000000 : ℝ)*(sp0) + (157886736449093/5000000000000 : ℝ)*(sp1) + (789453256077823/25000000000000 : ℝ)*(sp2) + (175782366886653/12500000000000 : ℝ)*(sp3) + (2183690693/20000000000000 : ℝ)*(sp7) + (1090212183/25000000000000 : ℝ)*(sp8) + (167239394399/50000000000000 : ℝ)*(sp9) + (128091729683/50000000000000 : ℝ)*(sp10) + (21972966461667/1562500000000 : ℝ)*(f.failure) + (1579034603885329/50000000000000 : ℝ)*(f.sum) + (5915486707/955000000000000000000000 : ℝ)*base66 + (81160420414737513/9550000000000000000000000000000 : ℝ)*base68 + (66671472737937513/9550000000000000000000000000000 : ℝ)*base70 + (120861790927337513/9550000000000000000000000000000 : ℝ)*base72 + (37104347631/95500000000000000000000000 : ℝ)*base74 + (40381627516237513/9550000000000000000000000000000 : ℝ)*base76 + (114151435066137513/9550000000000000000000000000000 : ℝ)*base78 + (126103032948037513/9550000000000000000000000000000 : ℝ)*base80 + (87469266303/95500000000000000000000000 : ℝ)*base81 + (474969/156250000000000000000 : ℝ)*base89 + (474969/156250000000000000000 : ℝ)*base91 + (474969/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (16053/20000 : ℝ) ≤ (15331168445277497922202749/19100000000000000000000000 : ℝ) := by norm_num
    linear_combination (11479459/100000000000000 : ℝ)*(lower2) + (67053051/100000000000000 : ℝ)*(lower3) + (98664649/100000000000000 : ℝ)*(upper4) + (15883683/50000000000000 : ℝ)*(lower5) + (2486434671739827/100000000000000 : ℝ)*(major0) + (2486434671739827/100000000000000 : ℝ)*(major1) + (2486434671739827/100000000000000 : ℝ)*(major2) + (3426432451/12500000000000 : ℝ)*(sp1) + (95516313141/100000000000000 : ℝ)*(sp2) + (34785062593/100000000000000 : ℝ)*(sp3) + (1710252635988407/50000000000000 : ℝ)*(sp8) + (684095572103441/20000000000000 : ℝ)*(sp9) + (427551219457959/12500000000000 : ℝ)*(sp10) + (381393330141789/25000000000000 : ℝ)*(sp11) + (1525608105629749/100000000000000 : ℝ)*(f.failure) + (1710252635988407/50000000000000 : ℝ)*(f.sum) + (690107821251/191000000000000000000000000 : ℝ)*base65 + (5012218858215243/38200000000000000000000000000000 : ℝ)*base68 + (144234725549815243/38200000000000000000000000000000 : ℝ)*base70 + (393008979103384757/38200000000000000000000000000000 : ℝ)*base71 + (13107305789/38200000000000000000000000 : ℝ)*base73 + (17536581905615243/38200000000000000000000000000000 : ℝ)*base76 + (102861212054584757/38200000000000000000000000000000 : ℝ)*base77 + (166431633146384757/38200000000000000000000000000000 : ℝ)*base79 + (52060309673/23875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31546657/10000000000000000000000 : ℝ)*base90 + (31546657/10000000000000000000000 : ℝ)*base92 + (31546657/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8597/10000 : ℝ) ≤ (-8209860019523691482806053812631/9550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53835049/100000000000000 : ℝ)*(upper3) + (692049/625000000000 : ℝ)*(lower4) + (9103253/100000000000000 : ℝ)*(upper5) + (1262693887587147/50000000000000 : ℝ)*(major0) + (1262693887587147/50000000000000 : ℝ)*(major1) + (1262693887587147/50000000000000 : ℝ)*(major2) + (20088673/2500000000000 : ℝ)*(sp4) + (59904763843/100000000000000 : ℝ)*(sp5) + (84089675201/100000000000000 : ℝ)*(sp6) + (5338507007/12500000000000 : ℝ)*(sp7) + (352992179235731/10000000000000 : ℝ)*(sp12) + (3529862691140387/100000000000000 : ℝ)*(sp13) + (882459626557257/25000000000000 : ℝ)*(sp14) + (61978638130509/4000000000000 : ℝ)*(sp15) + (1549508661318781/100000000000000 : ℝ)*(f.failure) + (352992259590423/10000000000000 : ℝ)*(f.sum) + (45225946427/95500000000000000000000000 : ℝ)*base65 + (84170678191370877/19100000000000000000000000000000 : ℝ)*base67 + (153046532426329123/19100000000000000000000000000000 : ℝ)*base70 + (5348062841370877/19100000000000000000000000000000 : ℝ)*base71 + (80268444723/23875000000000000000000000 : ℝ)*base74 + (76205341946529123/19100000000000000000000000000000 : ℝ)*base76 + (114772634874870877/19100000000000000000000000000000 : ℝ)*base77 + (175259740999370877/19100000000000000000000000000000 : ℝ)*base79 + (810182033889/191000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (24733367/10000000000000000000000 : ℝ)*base89 + (24733367/10000000000000000000000 : ℝ)*base91 + (24733367/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1507_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63733/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (16053/20000 : ℝ) ≤ X j i ∧ X j i ≤ (8597/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1507_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1507_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63733/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (16053/20000 : ℝ) ≤ X j i ∧ X j i ≤ (8597/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1507_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1507_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1507_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63733/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (16053/20000 : ℝ) ≤ X j i ∧ X j i ≤ (8597/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1507_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
