-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1038_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:44:59.526985+00:00
-- url     : https://prove2.me/submissions/7681510e-87f7-4f57-854a-6c6d0eb8ef95

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
theorem support_rectangle_w1038_s6_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217571121/10000000000 : ℝ)*x 0 + (269774697/500000000 : ℝ)*x 1 + (5263313993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217571121/10000000000 : ℝ)^8231 ≤ (1683147103597/12500000000000 : ℝ)^6183 := by
    have hnat : (2217571121 : ℕ)^8231*12500000000000^6183 ≤ 1683147103597^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217571121 10000000000 1683147103597 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269774697/500000000 : ℝ)^8231 ≤ (43981667774613/100000000000000 : ℝ)^6183 := by
    have hnat : (269774697 : ℕ)^8231*100000000000000^6183 ≤ 43981667774613^6183*500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269774697 500000000 43981667774613 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263313993/10000000000 : ℝ)^8231 ≤ (42553155383491/100000000000000 : ℝ)^6183 := by
    have hnat : (5263313993 : ℕ)^8231*100000000000000^6183 ≤ 42553155383491^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263313993 10000000000 42553155383491 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217571121/10000000000 : ℝ), (269774697/500000000 : ℝ), (5263313993/10000000000 : ℝ)] ![(1683147103597/12500000000000 : ℝ), (43981667774613/100000000000000 : ℝ), (42553155383491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217571121/10000000000 : ℝ)|^8231 ≤ (1683147103597/12500000000000 : ℝ)^6183
        have hw : |(-2217571121/10000000000 : ℝ)|=(2217571121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269774697/500000000 : ℝ)|^8231 ≤ (43981667774613/100000000000000 : ℝ)^6183
        have hw : |(269774697/500000000 : ℝ)|=(269774697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263313993/10000000000 : ℝ)|^8231 ≤ (42553155383491/100000000000000 : ℝ)^6183
        have hw : |(5263313993/10000000000 : ℝ)|=(5263313993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345199223/10000000000 : ℝ)*x 0 + (-285581529/1250000000 : ℝ)*x 1 + (1315828493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345199223/10000000000 : ℝ)^8231 ≤ (43436733876343/100000000000000 : ℝ)^6183 := by
    have hnat : (5345199223 : ℕ)^8231*100000000000000^6183 ≤ 43436733876343^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345199223 10000000000 43436733876343 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285581529/1250000000 : ℝ)^8231 ≤ (2802022189393/20000000000000 : ℝ)^6183 := by
    have hnat : (285581529 : ℕ)^8231*20000000000000^6183 ≤ 2802022189393^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285581529 1250000000 2802022189393 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315828493/2500000000 : ℝ)^8231 ≤ (1329786098671/3125000000000 : ℝ)^6183 := by
    have hnat : (1315828493 : ℕ)^8231*3125000000000^6183 ≤ 1329786098671^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315828493 2500000000 1329786098671 3125000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345199223/10000000000 : ℝ), (-285581529/1250000000 : ℝ), (1315828493/2500000000 : ℝ)] ![(43436733876343/100000000000000 : ℝ), (2802022189393/20000000000000 : ℝ), (1329786098671/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345199223/10000000000 : ℝ)|^8231 ≤ (43436733876343/100000000000000 : ℝ)^6183
        have hw : |(5345199223/10000000000 : ℝ)|=(5345199223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285581529/1250000000 : ℝ)|^8231 ≤ (2802022189393/20000000000000 : ℝ)^6183
        have hw : |(-285581529/1250000000 : ℝ)|=(285581529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315828493/2500000000 : ℝ)|^8231 ≤ (1329786098671/3125000000000 : ℝ)^6183
        have hw : |(1315828493/2500000000 : ℝ)|=(1315828493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336299771/2500000000 : ℝ)*x 0 + (657914259/1250000000 : ℝ)*x 1 + (-456930457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336299771/2500000000 : ℝ)^8231 ≤ (21718366186321/50000000000000 : ℝ)^6183 := by
    have hnat : (1336299771 : ℕ)^8231*50000000000000^6183 ≤ 21718366186321^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336299771 2500000000 21718366186321 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657914259/1250000000 : ℝ)^8231 ≤ (21276578116877/50000000000000 : ℝ)^6183 := by
    have hnat : (657914259 : ℕ)^8231*50000000000000^6183 ≤ 21276578116877^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657914259 1250000000 21276578116877 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456930457/2000000000 : ℝ)^8231 ≤ (14010111379629/100000000000000 : ℝ)^6183 := by
    have hnat : (456930457 : ℕ)^8231*100000000000000^6183 ≤ 14010111379629^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456930457 2000000000 14010111379629 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336299771/2500000000 : ℝ), (657914259/1250000000 : ℝ), (-456930457/2000000000 : ℝ)] ![(21718366186321/50000000000000 : ℝ), (21276578116877/50000000000000 : ℝ), (14010111379629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336299771/2500000000 : ℝ)|^8231 ≤ (21718366186321/50000000000000 : ℝ)^6183
        have hw : |(1336299771/2500000000 : ℝ)|=(1336299771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657914259/1250000000 : ℝ)|^8231 ≤ (21276578116877/50000000000000 : ℝ)^6183
        have hw : |(657914259/1250000000 : ℝ)|=(657914259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456930457/2000000000 : ℝ)|^8231 ≤ (14010111379629/100000000000000 : ℝ)^6183
        have hw : |(-456930457/2000000000 : ℝ)|=(456930457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379502111/10000000000 : ℝ)*x 0 + (3402101/8000000 : ℝ)*x 1 + (4510241559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379502111/10000000000 : ℝ)^8231 ≤ (33316055117519/100000000000000 : ℝ)^6183 := by
    have hnat : (4379502111 : ℕ)^8231*100000000000000^6183 ≤ 33316055117519^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379502111 10000000000 33316055117519 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3402101/8000000 : ℝ)^8231 ≤ (32037384260637/100000000000000 : ℝ)^6183 := by
    have hnat : (3402101 : ℕ)^8231*100000000000000^6183 ≤ 32037384260637^6183*8000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3402101 8000000 32037384260637 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510241559/10000000000 : ℝ)^8231 ≤ (1385862424363/4000000000000 : ℝ)^6183 := by
    have hnat : (4510241559 : ℕ)^8231*4000000000000^6183 ≤ 1385862424363^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510241559 10000000000 1385862424363 4000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379502111/10000000000 : ℝ), (3402101/8000000 : ℝ), (4510241559/10000000000 : ℝ)] ![(33316055117519/100000000000000 : ℝ), (32037384260637/100000000000000 : ℝ), (1385862424363/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379502111/10000000000 : ℝ)|^8231 ≤ (33316055117519/100000000000000 : ℝ)^6183
        have hw : |(4379502111/10000000000 : ℝ)|=(4379502111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3402101/8000000 : ℝ)|^8231 ≤ (32037384260637/100000000000000 : ℝ)^6183
        have hw : |(3402101/8000000 : ℝ)|=(3402101/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510241559/10000000000 : ℝ)|^8231 ≤ (1385862424363/4000000000000 : ℝ)^6183
        have hw : |(4510241559/10000000000 : ℝ)|=(4510241559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-443515281/2000000000 : ℝ)*x 0 + (2631823937/5000000000 : ℝ)*x 1 + (84299357/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443515281/2000000000 : ℝ)^8231 ≤ (3366304885217/25000000000000 : ℝ)^6183 := by
    have hnat : (443515281 : ℕ)^8231*25000000000000^6183 ≤ 3366304885217^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443515281 2000000000 3366304885217 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631823937/5000000000 : ℝ)^8231 ≤ (42556748920427/100000000000000 : ℝ)^6183 := by
    have hnat : (2631823937 : ℕ)^8231*100000000000000^6183 ≤ 42556748920427^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631823937 5000000000 42556748920427 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84299357/156250000 : ℝ)^8231 ≤ (43978031527141/100000000000000 : ℝ)^6183 := by
    have hnat : (84299357 : ℕ)^8231*100000000000000^6183 ≤ 43978031527141^6183*156250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84299357 156250000 43978031527141 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443515281/2000000000 : ℝ), (2631823937/5000000000 : ℝ), (84299357/156250000 : ℝ)] ![(3366304885217/25000000000000 : ℝ), (42556748920427/100000000000000 : ℝ), (43978031527141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443515281/2000000000 : ℝ)|^8231 ≤ (3366304885217/25000000000000 : ℝ)^6183
        have hw : |(-443515281/2000000000 : ℝ)|=(443515281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631823937/5000000000 : ℝ)|^8231 ≤ (42556748920427/100000000000000 : ℝ)^6183
        have hw : |(2631823937/5000000000 : ℝ)|=(2631823937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84299357/156250000 : ℝ)|^8231 ≤ (43978031527141/100000000000000 : ℝ)^6183
        have hw : |(84299357/156250000 : ℝ)|=(84299357/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062396131/2000000000 : ℝ)*x 0 + (-430561481/2000000000 : ℝ)*x 1 + (5395158879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062396131/2000000000 : ℝ)^8231 ≤ (21538873041569/50000000000000 : ℝ)^6183 := by
    have hnat : (1062396131 : ℕ)^8231*50000000000000^6183 ≤ 21538873041569^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062396131 2000000000 21538873041569 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430561481/2000000000 : ℝ)^8231 ≤ (6472111022847/50000000000000 : ℝ)^6183 := by
    have hnat : (430561481 : ℕ)^8231*50000000000000^6183 ≤ 6472111022847^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430561481 2000000000 6472111022847 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395158879/10000000000 : ℝ)^8231 ≤ (21989015931767/50000000000000 : ℝ)^6183 := by
    have hnat : (5395158879 : ℕ)^8231*50000000000000^6183 ≤ 21989015931767^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395158879 10000000000 21989015931767 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062396131/2000000000 : ℝ), (-430561481/2000000000 : ℝ), (5395158879/10000000000 : ℝ)] ![(21538873041569/50000000000000 : ℝ), (6472111022847/50000000000000 : ℝ), (21989015931767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062396131/2000000000 : ℝ)|^8231 ≤ (21538873041569/50000000000000 : ℝ)^6183
        have hw : |(1062396131/2000000000 : ℝ)|=(1062396131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430561481/2000000000 : ℝ)|^8231 ≤ (6472111022847/50000000000000 : ℝ)^6183
        have hw : |(-430561481/2000000000 : ℝ)|=(430561481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395158879/10000000000 : ℝ)|^8231 ≤ (21989015931767/50000000000000 : ℝ)^6183
        have hw : |(5395158879/10000000000 : ℝ)|=(5395158879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311980687/10000000000 : ℝ)*x 0 + (1348789703/2500000000 : ℝ)*x 1 + (-538201863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311980687/10000000000 : ℝ)^8231 ≤ (43077746428599/100000000000000 : ℝ)^6183 := by
    have hnat : (5311980687 : ℕ)^8231*100000000000000^6183 ≤ 43077746428599^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311980687 10000000000 43077746428599 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348789703/2500000000 : ℝ)^8231 ≤ (10994507784123/25000000000000 : ℝ)^6183 := by
    have hnat : (1348789703 : ℕ)^8231*25000000000000^6183 ≤ 10994507784123^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348789703 2500000000 10994507784123 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538201863/2500000000 : ℝ)^8231 ≤ (12944222421897/100000000000000 : ℝ)^6183 := by
    have hnat : (538201863 : ℕ)^8231*100000000000000^6183 ≤ 12944222421897^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538201863 2500000000 12944222421897 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311980687/10000000000 : ℝ), (1348789703/2500000000 : ℝ), (-538201863/2500000000 : ℝ)] ![(43077746428599/100000000000000 : ℝ), (10994507784123/25000000000000 : ℝ), (12944222421897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311980687/10000000000 : ℝ)|^8231 ≤ (43077746428599/100000000000000 : ℝ)^6183
        have hw : |(5311980687/10000000000 : ℝ)|=(5311980687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348789703/2500000000 : ℝ)|^8231 ≤ (10994507784123/25000000000000 : ℝ)^6183
        have hw : |(1348789703/2500000000 : ℝ)|=(1348789703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538201863/2500000000 : ℝ)|^8231 ≤ (12944222421897/100000000000000 : ℝ)^6183
        have hw : |(-538201863/2500000000 : ℝ)|=(538201863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s6_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379512491/10000000000 : ℝ)*x 0 + (281849413/625000000 : ℝ)*x 1 + (1063319873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379512491/10000000000 : ℝ)^8231 ≤ (16658080118077/50000000000000 : ℝ)^6183 := by
    have hnat : (4379512491 : ℕ)^8231*50000000000000^6183 ≤ 16658080118077^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379512491 10000000000 16658080118077 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281849413/625000000 : ℝ)^8231 ≤ (8659976005573/25000000000000 : ℝ)^6183 := by
    have hnat : (281849413 : ℕ)^8231*25000000000000^6183 ≤ 8659976005573^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281849413 625000000 8659976005573 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063319873/2500000000 : ℝ)^8231 ≤ (16021967862157/50000000000000 : ℝ)^6183 := by
    have hnat : (1063319873 : ℕ)^8231*50000000000000^6183 ≤ 16021967862157^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063319873 2500000000 16021967862157 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379512491/10000000000 : ℝ), (281849413/625000000 : ℝ), (1063319873/2500000000 : ℝ)] ![(16658080118077/50000000000000 : ℝ), (8659976005573/25000000000000 : ℝ), (16021967862157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379512491/10000000000 : ℝ)|^8231 ≤ (16658080118077/50000000000000 : ℝ)^6183
        have hw : |(4379512491/10000000000 : ℝ)|=(4379512491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281849413/625000000 : ℝ)|^8231 ≤ (8659976005573/25000000000000 : ℝ)^6183
        have hw : |(281849413/625000000 : ℝ)|=(281849413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063319873/2500000000 : ℝ)|^8231 ≤ (16021967862157/50000000000000 : ℝ)^6183
        have hw : |(1063319873/2500000000 : ℝ)|=(1063319873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11199/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11153/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (14855643181908241/100000000000000000000 : ℝ) := by
    have hpowers : (11153/100000 : ℝ)^4115 ≤ (14855643181908241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11153 : ℕ)^4115*100000000000000000000^1024 ≤ 14855643181908241^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11153 100000 14855643181908241 100000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11153/100000 : ℝ)) (X := (14855643181908241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (4115/1024 : ℝ) ≤ (18776396686703491/50000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^4115 ≤ (18776396686703491/50000000000000000000 : ℝ)^1024 := by
      have hnat : (439 : ℕ)^4115*50000000000000000000^1024 ≤ 18776396686703491^1024*3125^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 18776396686703491 50000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (18776396686703491/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014855643181908241/50000000000000000000 : ℝ) ≤ (5000369635028039/5000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50014855643181908241/50000000000000000000 : ℝ)^1024 ≤ (5000369635028039/5000000000000000 : ℝ)^4115 := by
      have hnat : (50014855643181908241 : ℕ)^1024*5000000000000000^4115 ≤ 5000369635028039^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014855643181908241 50000000000000000000 5000369635028039 5000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000369635028039/5000000000000000 : ℝ)) (X := (50014855643181908241/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052408436555315223/100000000000000000000 : ℝ) ≤ (400052156188497/400000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (100052408436555315223/100000000000000000000 : ℝ)^1024 ≤ (400052156188497/400000000000000 : ℝ)^4115 := by
      have hnat : (100052408436555315223 : ℕ)^1024*400000000000000^4115 ≤ 400052156188497^4115*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052408436555315223 100000000000000000000 400052156188497 400000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400052156188497/400000000000000 : ℝ)) (X := (100052408436555315223/100000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018776396686703491/25000000000000000000 : ℝ) ≤ (2500467134842193/2500000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (25018776396686703491/25000000000000000000 : ℝ)^1024 ≤ (2500467134842193/2500000000000000 : ℝ)^4115 := by
      have hnat : (25018776396686703491 : ℕ)^1024*2500000000000000^4115 ≤ 2500467134842193^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018776396686703491 25000000000000000000 2500467134842193 2500000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500467134842193/2500000000000000 : ℝ)) (X := (25018776396686703491/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14855643181908241/100000000000000000000 : ℝ) ≤ ((7234886361541967407/7237500000000000000 : ℝ)+2*(564634656347/289500000000000 : ℝ)*(11153/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (7234886361541967407/7237500000000000000 : ℝ)+2*(564634656347/289500000000000 : ℝ)*(11153/100000 : ℝ)=(5000369635028039/5000000000000000 : ℝ) by norm_num, show 1+2*(14855643181908241/100000000000000000000 : ℝ)=(50014855643181908241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18776396686703491/50000000000000000000 : ℝ)+(14855643181908241/100000000000000000000 : ℝ) ≤ ((7234886361541967407/7237500000000000000 : ℝ)+(564634656347/289500000000000 : ℝ)*((439/3125 : ℝ)+(11153/100000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (7234886361541967407/7237500000000000000 : ℝ)+(564634656347/289500000000000 : ℝ)*((439/3125 : ℝ)+(11153/100000 : ℝ))=(400052156188497/400000000000000 : ℝ) by norm_num, show 1+(18776396686703491/50000000000000000000 : ℝ)+(14855643181908241/100000000000000000000 : ℝ)=(100052408436555315223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18776396686703491/50000000000000000000 : ℝ) ≤ ((7234886361541967407/7237500000000000000 : ℝ)+2*(564634656347/289500000000000 : ℝ)*(439/3125 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (7234886361541967407/7237500000000000000 : ℝ)+2*(564634656347/289500000000000 : ℝ)*(439/3125 : ℝ)=(2500467134842193/2500000000000000 : ℝ) by norm_num, show 1+2*(18776396686703491/50000000000000000000 : ℝ)=(25018776396686703491/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7234886361541967407/7237500000000000000 : ℝ)*(X 1 0+X 2 0)+(564634656347/289500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (7234886361541967407/7237500000000000000 : ℝ)) (alpha := (564634656347/289500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7234886361541967407/7237500000000000000 : ℝ)*(X 0 1+X 2 1)+(564634656347/289500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (7234886361541967407/7237500000000000000 : ℝ)) (alpha := (564634656347/289500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7234886361541967407/7237500000000000000 : ℝ)*(X 0 2+X 1 2)+(564634656347/289500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (7234886361541967407/7237500000000000000 : ℝ)) (alpha := (564634656347/289500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2217571121/10000000000 : ℝ)*X 0 0+(269774697/500000000 : ℝ)*X 0 1+(5263313993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345199223/10000000000 : ℝ)*X 1 0+(-285581529/1250000000 : ℝ)*X 1 1+(1315828493/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336299771/2500000000 : ℝ)*X 2 0+(657914259/1250000000 : ℝ)*X 2 1+(-456930457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379502111/10000000000 : ℝ)*X 0 0+(3402101/8000000 : ℝ)*X 0 1+(4510241559/10000000000 : ℝ)*X 0 2+(4379502111/10000000000 : ℝ)*X 1 0+(3402101/8000000 : ℝ)*X 1 1+(4510241559/10000000000 : ℝ)*X 1 2+(4379502111/10000000000 : ℝ)*X 2 0+(3402101/8000000 : ℝ)*X 2 1+(4510241559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-443515281/2000000000 : ℝ)*X 0 0+(2631823937/5000000000 : ℝ)*X 0 1+(84299357/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062396131/2000000000 : ℝ)*X 1 0+(-430561481/2000000000 : ℝ)*X 1 1+(5395158879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311980687/10000000000 : ℝ)*X 2 0+(1348789703/2500000000 : ℝ)*X 2 1+(-538201863/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379512491/10000000000 : ℝ)*X 0 0+(281849413/625000000 : ℝ)*X 0 1+(1063319873/2500000000 : ℝ)*X 0 2+(4379512491/10000000000 : ℝ)*X 1 0+(281849413/625000000 : ℝ)*X 1 1+(1063319873/2500000000 : ℝ)*X 1 2+(4379512491/10000000000 : ℝ)*X 2 0+(281849413/625000000 : ℝ)*X 2 1+(1063319873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96342120332849442057646709/12062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (342825417/20000000000000 : ℝ)*(base19) + (180338777/12500000000000 : ℝ)*(base23) + (39916823/100000000000000 : ℝ)*(lower2) + (132001883/50000000000000 : ℝ)*(upper3) + (44417511/50000000000000 : ℝ)*(upper5) + (1144733981923513/20000000000000 : ℝ)*(major0) + (1144733981923513/20000000000000 : ℝ)*(major1) + (1144733981923513/20000000000000 : ℝ)*(major2) + (1891373374357163/25000000000000 : ℝ)*(sp0) + (1513106427309633/20000000000000 : ℝ)*(sp1) + (3782766203982517/50000000000000 : ℝ)*(sp2) + (194088990563013/5000000000000 : ℝ)*(sp3) + (20176623299/50000000000000 : ℝ)*(sp4) + (25891069229/100000000000000 : ℝ)*(sp7) + (3881805702329489/100000000000000 : ℝ)*(f.failure) + (30262135402701/400000000000 : ℝ)*(f.sum) + (5278359775949/723750000000000000000000000 : ℝ)*base65 + (255790376650261403/48250000000000000000000000000000 : ℝ)*base68 + (505213651771738597/48250000000000000000000000000000 : ℝ)*base69 + (333158950427238597/48250000000000000000000000000000 : ℝ)*base71 + (15954438314029/2895000000000000000000000000 : ℝ)*base74 + (679920395741738597/48250000000000000000000000000000 : ℝ)*base75 + (208637615233988597/48250000000000000000000000000000 : ℝ)*base77 + (403914652152738597/48250000000000000000000000000000 : ℝ)*base79 + (7623534936401/2895000000000000000000000000 : ℝ)*base81 + (681519/2000000000000000000000 : ℝ)*base90 + (681519/2000000000000000000000 : ℝ)*base92 + (681519/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (417217679664652428084561903/60312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274031367/20000000000000 : ℝ)*(base19) + (19037183/1250000000000 : ℝ)*(base23) + (65559869/50000000000000 : ℝ)*(upper3) + (31878483/50000000000000 : ℝ)*(lower4) + (20598067/10000000000000 : ℝ)*(upper5) + (5752718539305329/100000000000000 : ℝ)*(major0) + (5752718539305329/100000000000000 : ℝ)*(major1) + (5752718539305329/100000000000000 : ℝ)*(major2) + (19848620261/50000000000000 : ℝ)*(sp1) + (37616364597/100000000000000 : ℝ)*(sp2) + (7603930300232193/100000000000000 : ℝ)*(sp4) + (7603889232834837/100000000000000 : ℝ)*(sp5) + (7603891160892957/100000000000000 : ℝ)*(sp6) + (3901506547791829/100000000000000 : ℝ)*(sp7) + (3901506547791829/100000000000000 : ℝ)*(f.failure) + (7603930300232193/100000000000000 : ℝ)*(f.sum) + (4762963347013/14475000000000000000000000000 : ℝ)*base65 + (1433596560146337699/241250000000000000000000000000000 : ℝ)*base68 + (2400313009988837699/241250000000000000000000000000000 : ℝ)*base70 + (901732639306162301/241250000000000000000000000000000 : ℝ)*base71 + (3982423411619/7237500000000000000000000000 : ℝ)*base73 + (6248213705612587699/241250000000000000000000000000000 : ℝ)*base76 + (584405469991337699/241250000000000000000000000000000 : ℝ)*base78 + (2212638258268837699/241250000000000000000000000000000 : ℝ)*base80 + (9019924498319/7237500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5624341/2000000000000000000000 : ℝ)*base89 + (5624341/2000000000000000000000 : ℝ)*base91 + (5624341/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1038_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1038_s7_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-554405081/2500000000 : ℝ)*x 0 + (5394964361/10000000000 : ℝ)*x 1 + (5263810971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554405081/2500000000 : ℝ)^8231 ≤ (168319681901/1250000000000 : ℝ)^6183 := by
    have hnat : (554405081 : ℕ)^8231*1250000000000^6183 ≤ 168319681901^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554405081 2500000000 168319681901 1250000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394964361/10000000000 : ℝ)^8231 ≤ (43975921087723/100000000000000 : ℝ)^6183 := by
    have hnat : (5394964361 : ℕ)^8231*100000000000000^6183 ≤ 43975921087723^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394964361 10000000000 43975921087723 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263810971/10000000000 : ℝ)^8231 ≤ (21279252174517/50000000000000 : ℝ)^6183 := by
    have hnat : (5263810971 : ℕ)^8231*50000000000000^6183 ≤ 21279252174517^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263810971 10000000000 21279252174517 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554405081/2500000000 : ℝ), (5394964361/10000000000 : ℝ), (5263810971/10000000000 : ℝ)] ![(168319681901/1250000000000 : ℝ), (43975921087723/100000000000000 : ℝ), (21279252174517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554405081/2500000000 : ℝ)|^8231 ≤ (168319681901/1250000000000 : ℝ)^6183
        have hw : |(-554405081/2500000000 : ℝ)|=(554405081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394964361/10000000000 : ℝ)|^8231 ≤ (43975921087723/100000000000000 : ℝ)^6183
        have hw : |(5394964361/10000000000 : ℝ)|=(5394964361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263810971/10000000000 : ℝ)|^8231 ≤ (21279252174517/50000000000000 : ℝ)^6183
        have hw : |(5263810971/10000000000 : ℝ)|=(5263810971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534506641/1000000000 : ℝ)*x 0 + (-2284172917/10000000000 : ℝ)*x 1 + (5263811/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534506641/1000000000 : ℝ)^8231 ≤ (43435297112401/100000000000000 : ℝ)^6183 := by
    have hnat : (534506641 : ℕ)^8231*100000000000000^6183 ≤ 43435297112401^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534506641 1000000000 43435297112401 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284172917/10000000000 : ℝ)^8231 ≤ (700309910453/5000000000000 : ℝ)^6183 := by
    have hnat : (2284172917 : ℕ)^8231*5000000000000^6183 ≤ 700309910453^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284172917 10000000000 700309910453 5000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263811/10000000 : ℝ)^8231 ≤ (8511700932233/20000000000000 : ℝ)^6183 := by
    have hnat : (5263811 : ℕ)^8231*20000000000000^6183 ≤ 8511700932233^6183*10000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263811 10000000 8511700932233 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534506641/1000000000 : ℝ), (-2284172917/10000000000 : ℝ), (5263811/10000000 : ℝ)] ![(43435297112401/100000000000000 : ℝ), (700309910453/5000000000000 : ℝ), (8511700932233/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534506641/1000000000 : ℝ)|^8231 ≤ (43435297112401/100000000000000 : ℝ)^6183
        have hw : |(534506641/1000000000 : ℝ)|=(534506641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284172917/10000000000 : ℝ)|^8231 ≤ (700309910453/5000000000000 : ℝ)^6183
        have hw : |(-2284172917/10000000000 : ℝ)|=(2284172917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263811/10000000 : ℝ)|^8231 ≤ (8511700932233/20000000000000 : ℝ)^6183
        have hw : |(5263811/10000000 : ℝ)|=(5263811/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336266613/2500000000 : ℝ)*x 0 + (2631905483/5000000000 : ℝ)*x 1 + (-2284172907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336266613/2500000000 : ℝ)^8231 ≤ (43435297566753/100000000000000 : ℝ)^6183 := by
    have hnat : (1336266613 : ℕ)^8231*100000000000000^6183 ≤ 43435297566753^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336266613 2500000000 43435297566753 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631905483/5000000000 : ℝ)^8231 ≤ (21279252147609/50000000000000 : ℝ)^6183 := by
    have hnat : (2631905483 : ℕ)^8231*50000000000000^6183 ≤ 21279252147609^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631905483 5000000000 21279252147609 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284172907/10000000000 : ℝ)^8231 ≤ (14006198127431/100000000000000 : ℝ)^6183 := by
    have hnat : (2284172907 : ℕ)^8231*100000000000000^6183 ≤ 14006198127431^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284172907 10000000000 14006198127431 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336266613/2500000000 : ℝ), (2631905483/5000000000 : ℝ), (-2284172907/10000000000 : ℝ)] ![(43435297566753/100000000000000 : ℝ), (21279252147609/50000000000000 : ℝ), (14006198127431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336266613/2500000000 : ℝ)|^8231 ≤ (43435297566753/100000000000000 : ℝ)^6183
        have hw : |(1336266613/2500000000 : ℝ)|=(1336266613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631905483/5000000000 : ℝ)|^8231 ≤ (21279252147609/50000000000000 : ℝ)^6183
        have hw : |(2631905483/5000000000 : ℝ)|=(2631905483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284172907/10000000000 : ℝ)|^8231 ≤ (14006198127431/100000000000000 : ℝ)^6183
        have hw : |(-2284172907/10000000000 : ℝ)|=(2284172907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379528513/10000000000 : ℝ)*x 0 + (4253623201/10000000000 : ℝ)*x 1 + (225461881/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379528513/10000000000 : ℝ)^8231 ≤ (4164540311461/12500000000000 : ℝ)^6183 := by
    have hnat : (4379528513 : ℕ)^8231*12500000000000^6183 ≤ 4164540311461^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379528513 10000000000 4164540311461 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4253623201/10000000000 : ℝ)^8231 ≤ (32047382968133/100000000000000 : ℝ)^6183 := by
    have hnat : (4253623201 : ℕ)^8231*100000000000000^6183 ≤ 32047382968133^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253623201 10000000000 32047382968133 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225461881/500000000 : ℝ)^8231 ≤ (34636294520769/100000000000000 : ℝ)^6183 := by
    have hnat : (225461881 : ℕ)^8231*100000000000000^6183 ≤ 34636294520769^6183*500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225461881 500000000 34636294520769 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379528513/10000000000 : ℝ), (4253623201/10000000000 : ℝ), (225461881/500000000 : ℝ)] ![(4164540311461/12500000000000 : ℝ), (32047382968133/100000000000000 : ℝ), (34636294520769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379528513/10000000000 : ℝ)|^8231 ≤ (4164540311461/12500000000000 : ℝ)^6183
        have hw : |(4379528513/10000000000 : ℝ)|=(4379528513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4253623201/10000000000 : ℝ)|^8231 ≤ (32047382968133/100000000000000 : ℝ)^6183
        have hw : |(4253623201/10000000000 : ℝ)|=(4253623201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225461881/500000000 : ℝ)|^8231 ≤ (34636294520769/100000000000000 : ℝ)^6183
        have hw : |(225461881/500000000 : ℝ)|=(225461881/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217625533/10000000000 : ℝ)*x 0 + (5264139831/10000000000 : ℝ)*x 1 + (1348658571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217625533/10000000000 : ℝ)^8231 ≤ (6732808329117/50000000000000 : ℝ)^6183 := by
    have hnat : (2217625533 : ℕ)^8231*50000000000000^6183 ≤ 6732808329117^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217625533 10000000000 6732808329117 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264139831/10000000000 : ℝ)^8231 ≤ (42562043955447/100000000000000 : ℝ)^6183 := by
    have hnat : (5264139831 : ℕ)^8231*100000000000000^6183 ≤ 42562043955447^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264139831 10000000000 42562043955447 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348658571/2500000000 : ℝ)^8231 ≤ (21986169688189/50000000000000 : ℝ)^6183 := by
    have hnat : (1348658571 : ℕ)^8231*50000000000000^6183 ≤ 21986169688189^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348658571 2500000000 21986169688189 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217625533/10000000000 : ℝ), (5264139831/10000000000 : ℝ), (1348658571/2500000000 : ℝ)] ![(6732808329117/50000000000000 : ℝ), (42562043955447/100000000000000 : ℝ), (21986169688189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217625533/10000000000 : ℝ)|^8231 ≤ (6732808329117/50000000000000 : ℝ)^6183
        have hw : |(-2217625533/10000000000 : ℝ)|=(2217625533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264139831/10000000000 : ℝ)|^8231 ≤ (42562043955447/100000000000000 : ℝ)^6183
        have hw : |(5264139831/10000000000 : ℝ)|=(5264139831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348658571/2500000000 : ℝ)|^8231 ≤ (21986169688189/50000000000000 : ℝ)^6183
        have hw : |(1348658571/2500000000 : ℝ)|=(1348658571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656053063/5000000000 : ℝ)*x 0 + (-538337413/2500000000 : ℝ)*x 1 + (5394634047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656053063/5000000000 : ℝ)^8231 ≤ (43079100632701/100000000000000 : ℝ)^6183 := by
    have hnat : (2656053063 : ℕ)^8231*100000000000000^6183 ≤ 43079100632701^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656053063 5000000000 43079100632701 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538337413/2500000000 : ℝ)^8231 ≤ (1294856254213/10000000000000 : ℝ)^6183 := by
    have hnat : (538337413 : ℕ)^8231*10000000000000^6183 ≤ 1294856254213^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538337413 2500000000 1294856254213 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394634047/10000000000 : ℝ)^8231 ≤ (8794467360937/20000000000000 : ℝ)^6183 := by
    have hnat : (5394634047 : ℕ)^8231*20000000000000^6183 ≤ 8794467360937^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394634047 10000000000 8794467360937 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656053063/5000000000 : ℝ), (-538337413/2500000000 : ℝ), (5394634047/10000000000 : ℝ)] ![(43079100632701/100000000000000 : ℝ), (1294856254213/10000000000000 : ℝ), (8794467360937/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656053063/5000000000 : ℝ)|^8231 ≤ (43079100632701/100000000000000 : ℝ)^6183
        have hw : |(2656053063/5000000000 : ℝ)|=(2656053063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538337413/2500000000 : ℝ)|^8231 ≤ (1294856254213/10000000000000 : ℝ)^6183
        have hw : |(-538337413/2500000000 : ℝ)|=(538337413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394634047/10000000000 : ℝ)|^8231 ≤ (8794467360937/20000000000000 : ℝ)^6183
        have hw : |(5394634047/10000000000 : ℝ)|=(5394634047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656052977/5000000000 : ℝ)*x 0 + (337164649/625000000 : ℝ)*x 1 + (-538337357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656052977/5000000000 : ℝ)^8231 ≤ (43079098775831/100000000000000 : ℝ)^6183 := by
    have hnat : (2656052977 : ℕ)^8231*100000000000000^6183 ≤ 43079098775831^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656052977 5000000000 43079098775831 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337164649/625000000 : ℝ)^8231 ≤ (43972340461481/100000000000000 : ℝ)^6183 := by
    have hnat : (337164649 : ℕ)^8231*100000000000000^6183 ≤ 43972340461481^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337164649 625000000 43972340461481 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538337357/2500000000 : ℝ)^8231 ≤ (6474280374507/50000000000000 : ℝ)^6183 := by
    have hnat : (538337357 : ℕ)^8231*50000000000000^6183 ≤ 6474280374507^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538337357 2500000000 6474280374507 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656052977/5000000000 : ℝ), (337164649/625000000 : ℝ), (-538337357/2500000000 : ℝ)] ![(43079098775831/100000000000000 : ℝ), (43972340461481/100000000000000 : ℝ), (6474280374507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656052977/5000000000 : ℝ)|^8231 ≤ (43079098775831/100000000000000 : ℝ)^6183
        have hw : |(2656052977/5000000000 : ℝ)|=(2656052977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337164649/625000000 : ℝ)|^8231 ≤ (43972340461481/100000000000000 : ℝ)^6183
        have hw : |(337164649/625000000 : ℝ)|=(337164649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538337357/2500000000 : ℝ)|^8231 ≤ (6474280374507/50000000000000 : ℝ)^6183
        have hw : |(-538337357/2500000000 : ℝ)|=(538337357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s7_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379538003/10000000000 : ℝ)*x 0 + (563574673/1250000000 : ℝ)*x 1 + (53178329/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379538003/10000000000 : ℝ)^8231 ≤ (33316418597449/100000000000000 : ℝ)^6183 := by
    have hnat : (4379538003 : ℕ)^8231*100000000000000^6183 ≤ 33316418597449^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379538003 10000000000 33316418597449 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563574673/1250000000 : ℝ)^8231 ≤ (8657436996287/25000000000000 : ℝ)^6183 := by
    have hnat : (563574673 : ℕ)^8231*25000000000000^6183 ≤ 8657436996287^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563574673 1250000000 8657436996287 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53178329/125000000 : ℝ)^8231 ≤ (8013458351231/25000000000000 : ℝ)^6183 := by
    have hnat : (53178329 : ℕ)^8231*25000000000000^6183 ≤ 8013458351231^6183*125000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53178329 125000000 8013458351231 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379538003/10000000000 : ℝ), (563574673/1250000000 : ℝ), (53178329/125000000 : ℝ)] ![(33316418597449/100000000000000 : ℝ), (8657436996287/25000000000000 : ℝ), (8013458351231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379538003/10000000000 : ℝ)|^8231 ≤ (33316418597449/100000000000000 : ℝ)^6183
        have hw : |(4379538003/10000000000 : ℝ)|=(4379538003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563574673/1250000000 : ℝ)|^8231 ≤ (8657436996287/25000000000000 : ℝ)^6183
        have hw : |(563574673/1250000000 : ℝ)|=(563574673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53178329/125000000 : ℝ)|^8231 ≤ (8013458351231/25000000000000 : ℝ)^6183
        have hw : |(53178329/125000000 : ℝ)|=(53178329/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1121/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3497/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11199/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (94396265682783/625000000000000000 : ℝ) := by
    have hpowers : (11199/100000 : ℝ)^4115 ≤ (94396265682783/625000000000000000 : ℝ)^1024 := by
      have hnat : (11199 : ℕ)^4115*625000000000000000^1024 ≤ 94396265682783^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11199 100000 94396265682783 625000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11199/100000 : ℝ)) (X := (94396265682783/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13999/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (9257296198762319/25000000000000000000 : ℝ) := by
    have hpowers : (13999/100000 : ℝ)^4115 ≤ (9257296198762319/25000000000000000000 : ℝ)^1024 := by
      have hnat : (13999 : ℕ)^4115*25000000000000000000^1024 ≤ 9257296198762319^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13999 100000 9257296198762319 25000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13999/100000 : ℝ)) (X := (9257296198762319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312594396265682783/312500000000000000 : ℝ) ≤ (5000375799024943/5000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (312594396265682783/312500000000000000 : ℝ)^1024 ≤ (5000375799024943/5000000000000000 : ℝ)^4115 := by
      have hnat : (312594396265682783 : ℕ)^1024*5000000000000000^4115 ≤ 5000375799024943^4115*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312594396265682783 312500000000000000 5000375799024943 5000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000375799024943/5000000000000000 : ℝ)) (X := (312594396265682783/312500000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013033146826073639/25000000000000000000 : ℝ) ≤ (2500324260754187/2500000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (25013033146826073639/25000000000000000000 : ℝ)^1024 ≤ (2500324260754187/2500000000000000 : ℝ)^4115 := by
      have hnat : (25013033146826073639 : ℕ)^1024*2500000000000000^4115 ≤ 2500324260754187^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013033146826073639 25000000000000000000 2500324260754187 2500000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500324260754187/2500000000000000 : ℝ)) (X := (25013033146826073639/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509257296198762319/12500000000000000000 : ℝ) ≤ (1000184248798361/1000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (12509257296198762319/12500000000000000000 : ℝ)^1024 ≤ (1000184248798361/1000000000000000 : ℝ)^4115 := by
      have hnat : (12509257296198762319 : ℕ)^1024*1000000000000000^4115 ≤ 1000184248798361^4115*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509257296198762319 12500000000000000000 1000184248798361 1000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000184248798361/1000000000000000 : ℝ)) (X := (12509257296198762319/12500000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(94396265682783/625000000000000000 : ℝ) ≤ ((6997471899542976431/7000000000000000000 : ℝ)+2*(272722483431/140000000000000 : ℝ)*(11199/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (6997471899542976431/7000000000000000000 : ℝ)+2*(272722483431/140000000000000 : ℝ)*(11199/100000 : ℝ)=(5000375799024943/5000000000000000 : ℝ) by norm_num, show 1+2*(94396265682783/625000000000000000 : ℝ)=(312594396265682783/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9257296198762319/25000000000000000000 : ℝ)+(94396265682783/625000000000000000 : ℝ) ≤ ((6997471899542976431/7000000000000000000 : ℝ)+(272722483431/140000000000000 : ℝ)*((13999/100000 : ℝ)+(11199/100000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (6997471899542976431/7000000000000000000 : ℝ)+(272722483431/140000000000000 : ℝ)*((13999/100000 : ℝ)+(11199/100000 : ℝ))=(2500324260754187/2500000000000000 : ℝ) by norm_num, show 1+(9257296198762319/25000000000000000000 : ℝ)+(94396265682783/625000000000000000 : ℝ)=(25013033146826073639/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9257296198762319/25000000000000000000 : ℝ) ≤ ((6997471899542976431/7000000000000000000 : ℝ)+2*(272722483431/140000000000000 : ℝ)*(13999/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (6997471899542976431/7000000000000000000 : ℝ)+2*(272722483431/140000000000000 : ℝ)*(13999/100000 : ℝ)=(1000184248798361/1000000000000000 : ℝ) by norm_num, show 1+2*(9257296198762319/25000000000000000000 : ℝ)=(12509257296198762319/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6997471899542976431/7000000000000000000 : ℝ)*(X 1 0+X 2 0)+(272722483431/140000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (6997471899542976431/7000000000000000000 : ℝ)) (alpha := (272722483431/140000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6997471899542976431/7000000000000000000 : ℝ)*(X 0 1+X 2 1)+(272722483431/140000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (6997471899542976431/7000000000000000000 : ℝ)) (alpha := (272722483431/140000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6997471899542976431/7000000000000000000 : ℝ)*(X 0 2+X 1 2)+(272722483431/140000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (11199/100000 : ℝ)) (hi := (13999/100000 : ℝ)) (c := (6997471899542976431/7000000000000000000 : ℝ)) (alpha := (272722483431/140000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-554405081/2500000000 : ℝ)*X 0 0+(5394964361/10000000000 : ℝ)*X 0 1+(5263810971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534506641/1000000000 : ℝ)*X 1 0+(-2284172917/10000000000 : ℝ)*X 1 1+(5263811/10000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336266613/2500000000 : ℝ)*X 2 0+(2631905483/5000000000 : ℝ)*X 2 1+(-2284172907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379528513/10000000000 : ℝ)*X 0 0+(4253623201/10000000000 : ℝ)*X 0 1+(225461881/500000000 : ℝ)*X 0 2+(4379528513/10000000000 : ℝ)*X 1 0+(4253623201/10000000000 : ℝ)*X 1 1+(225461881/500000000 : ℝ)*X 1 2+(4379528513/10000000000 : ℝ)*X 2 0+(4253623201/10000000000 : ℝ)*X 2 1+(225461881/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2217625533/10000000000 : ℝ)*X 0 0+(5264139831/10000000000 : ℝ)*X 0 1+(1348658571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656053063/5000000000 : ℝ)*X 1 0+(-538337413/2500000000 : ℝ)*X 1 1+(5394634047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656052977/5000000000 : ℝ)*X 2 0+(337164649/625000000 : ℝ)*X 2 1+(-538337357/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379538003/10000000000 : ℝ)*X 0 0+(563574673/1250000000 : ℝ)*X 0 1+(53178329/125000000 : ℝ)*X 0 2+(4379538003/10000000000 : ℝ)*X 1 0+(563574673/1250000000 : ℝ)*X 1 1+(53178329/125000000 : ℝ)*X 1 2+(4379538003/10000000000 : ℝ)*X 2 0+(563574673/1250000000 : ℝ)*X 2 1+(53178329/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (395107706340483576324169449/87500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209547759/25000000000000 : ℝ)*(base19) + (48393563/6250000000000 : ℝ)*(base23) + (8271943/12500000000000 : ℝ)*(lower2) + (120635153/100000000000000 : ℝ)*(upper3) + (13954263/25000000000000 : ℝ)*(upper5) + (2884218165078507/50000000000000 : ℝ)*(major0) + (2884218165078507/50000000000000 : ℝ)*(major1) + (2884218165078507/50000000000000 : ℝ)*(major2) + (3812341653617793/50000000000000 : ℝ)*(sp0) + (1906176320747899/25000000000000 : ℝ)*(sp1) + (953088168360703/12500000000000 : ℝ)*(sp2) + (97803830418389/2500000000000 : ℝ)*(sp3) + (22813947047/100000000000000 : ℝ)*(sp4) + (13171878601/100000000000000 : ℝ)*(sp7) + (48902079857677/1250000000000 : ℝ)*(f.failure) + (953088265147829/12500000000000 : ℝ)*(f.sum) + (18918561370483/3500000000000000000000000000 : ℝ)*base66 + (352190020570216931/50000000000000000000000000000000 : ℝ)*base67 + (268396424220216931/50000000000000000000000000000000 : ℝ)*base69 + (44010045770216931/50000000000000000000000000000000 : ℝ)*base71 + (9312765375517/3500000000000000000000000000 : ℝ)*base73 + (1690537291920216931/50000000000000000000000000000000 : ℝ)*base75 + (327569738629783069/50000000000000000000000000000000 : ℝ)*base78 + (891166361520216931/50000000000000000000000000000000 : ℝ)*base79 + (20064433785517/3500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (200467/25000000000000000000 : ℝ)*base90 + (200467/25000000000000000000 : ℝ)*base92 + (200467/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2846759887057349296730393787/350000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1450934371/100000000000000 : ℝ)*(base19) + (1676383749/100000000000000 : ℝ)*(base23) + (167287811/100000000000000 : ℝ)*(upper2) + (128097103/100000000000000 : ℝ)*(upper3) + (5797520240872147/100000000000000 : ℝ)*(major0) + (5797520240872147/100000000000000 : ℝ)*(major1) + (5797520240872147/100000000000000 : ℝ)*(major2) + (6850754713/25000000000000 : ℝ)*(sp1) + (6621583591/12500000000000 : ℝ)*(sp2) + (943644299/25000000000000 : ℝ)*(sp3) + (957893631109539/12500000000000 : ℝ)*(sp4) + (478945012182693/6250000000000 : ℝ)*(sp5) + (1532618879964767/20000000000000 : ℝ)*(sp6) + (1965943693585389/50000000000000 : ℝ)*(sp7) + (1965945580873987/50000000000000 : ℝ)*(f.failure) + (957893631109539/12500000000000 : ℝ)*(f.sum) + (33264055794357/7000000000000000000000000000 : ℝ)*base65 + (130141331789031051/100000000000000000000000000000000 : ℝ)*base67 + (1258597464989031051/100000000000000000000000000000000 : ℝ)*base69 + (2011830144789031051/100000000000000000000000000000000 : ℝ)*base71 + (9609789480357/7000000000000000000000000000 : ℝ)*base73 + (4354050612189031051/100000000000000000000000000000000 : ℝ)*base75 + (1700697320989031051/100000000000000000000000000000000 : ℝ)*base77 + (1852758270189031051/100000000000000000000000000000000 : ℝ)*base79 + (50795204268357/7000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10220477/1000000000000000000000 : ℝ)*base90 + (10220477/1000000000000000000000 : ℝ)*base92 + (10220477/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1038_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1038_s8_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-6930091/31250000 : ℝ)*x 0 + (5394844887/10000000000 : ℝ)*x 1 + (1052784963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6930091/31250000 : ℝ)^8231 ≤ (13465645653219/100000000000000 : ℝ)^6183 := by
    have hnat : (6930091 : ℕ)^8231*100000000000000^6183 ≤ 13465645653219^6183*31250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6930091 31250000 13465645653219 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394844887/10000000000 : ℝ)^8231 ≤ (43974624650383/100000000000000 : ℝ)^6183 := by
    have hnat : (5394844887 : ℕ)^8231*100000000000000^6183 ≤ 43974624650383^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394844887 10000000000 43974624650383 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052784963/2000000000 : ℝ)^8231 ≤ (42559729673569/100000000000000 : ℝ)^6183 := by
    have hnat : (1052784963 : ℕ)^8231*100000000000000^6183 ≤ 42559729673569^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052784963 2000000000 42559729673569 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6930091/31250000 : ℝ), (5394844887/10000000000 : ℝ), (1052784963/2000000000 : ℝ)] ![(13465645653219/100000000000000 : ℝ), (43974624650383/100000000000000 : ℝ), (42559729673569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6930091/31250000 : ℝ)|^8231 ≤ (13465645653219/100000000000000 : ℝ)^6183
        have hw : |(-6930091/31250000 : ℝ)|=(6930091/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394844887/10000000000 : ℝ)|^8231 ≤ (43974624650383/100000000000000 : ℝ)^6183
        have hw : |(5394844887/10000000000 : ℝ)|=(5394844887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052784963/2000000000 : ℝ)|^8231 ≤ (42559729673569/100000000000000 : ℝ)^6183
        have hw : |(1052784963/2000000000 : ℝ)|=(1052784963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345037191/10000000000 : ℝ)*x 0 + (-114203079/500000000 : ℝ)*x 1 + (2631962403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345037191/10000000000 : ℝ)^8231 ≤ (21717490512203/50000000000000 : ℝ)^6183 := by
    have hnat : (5345037191 : ℕ)^8231*50000000000000^6183 ≤ 21717490512203^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345037191 10000000000 21717490512203 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114203079/500000000 : ℝ)^8231 ≤ (2801057876649/20000000000000 : ℝ)^6183 := by
    have hnat : (114203079 : ℕ)^8231*20000000000000^6183 ≤ 2801057876649^6183*500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114203079 500000000 2801057876649 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631962403/5000000000 : ℝ)^8231 ≤ (425597295767/1000000000000 : ℝ)^6183 := by
    have hnat : (2631962403 : ℕ)^8231*1000000000000^6183 ≤ 425597295767^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631962403 5000000000 425597295767 1000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345037191/10000000000 : ℝ), (-114203079/500000000 : ℝ), (2631962403/5000000000 : ℝ)] ![(21717490512203/50000000000000 : ℝ), (2801057876649/20000000000000 : ℝ), (425597295767/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345037191/10000000000 : ℝ)|^8231 ≤ (21717490512203/50000000000000 : ℝ)^6183
        have hw : |(5345037191/10000000000 : ℝ)|=(5345037191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114203079/500000000 : ℝ)|^8231 ≤ (2801057876649/20000000000000 : ℝ)^6183
        have hw : |(-114203079/500000000 : ℝ)|=(114203079/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631962403/5000000000 : ℝ)|^8231 ≤ (425597295767/1000000000000 : ℝ)^6183
        have hw : |(2631962403/5000000000 : ℝ)|=(2631962403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345037197/10000000000 : ℝ)*x 0 + (5263924809/10000000000 : ℝ)*x 1 + (-17844231/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345037197/10000000000 : ℝ)^8231 ≤ (43434981089313/100000000000000 : ℝ)^6183 := by
    have hnat : (5345037197 : ℕ)^8231*100000000000000^6183 ≤ 43434981089313^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345037197 10000000000 43434981089313 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263924809/10000000000 : ℝ)^8231 ≤ (42559729608989/100000000000000 : ℝ)^6183 := by
    have hnat : (5263924809 : ℕ)^8231*100000000000000^6183 ≤ 42559729608989^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263924809 10000000000 42559729608989 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17844231/78125000 : ℝ)^8231 ≤ (3501322321323/25000000000000 : ℝ)^6183 := by
    have hnat : (17844231 : ℕ)^8231*25000000000000^6183 ≤ 3501322321323^6183*78125000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17844231 78125000 3501322321323 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345037197/10000000000 : ℝ), (5263924809/10000000000 : ℝ), (-17844231/78125000 : ℝ)] ![(43434981089313/100000000000000 : ℝ), (42559729608989/100000000000000 : ℝ), (3501322321323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345037197/10000000000 : ℝ)|^8231 ≤ (43434981089313/100000000000000 : ℝ)^6183
        have hw : |(5345037197/10000000000 : ℝ)|=(5345037197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263924809/10000000000 : ℝ)|^8231 ≤ (42559729608989/100000000000000 : ℝ)^6183
        have hw : |(5263924809/10000000000 : ℝ)|=(5263924809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17844231/78125000 : ℝ)|^8231 ≤ (3501322321323/25000000000000 : ℝ)^6183
        have hw : |(-17844231/78125000 : ℝ)|=(17844231/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547441809/1250000000 : ℝ)*x 0 + (1063462451/2500000000 : ℝ)*x 1 + (90180189/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547441809/1250000000 : ℝ)^8231 ≤ (33316382838807/100000000000000 : ℝ)^6183 := by
    have hnat : (547441809 : ℕ)^8231*100000000000000^6183 ≤ 33316382838807^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547441809 1250000000 33316382838807 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063462451/2500000000 : ℝ)^8231 ≤ (6409931148577/20000000000000 : ℝ)^6183 := by
    have hnat : (1063462451 : ℕ)^8231*20000000000000^6183 ≤ 6409931148577^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063462451 2500000000 6409931148577 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90180189/200000000 : ℝ)^8231 ≤ (34633961403543/100000000000000 : ℝ)^6183 := by
    have hnat : (90180189 : ℕ)^8231*100000000000000^6183 ≤ 34633961403543^6183*200000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90180189 200000000 34633961403543 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547441809/1250000000 : ℝ), (1063462451/2500000000 : ℝ), (90180189/200000000 : ℝ)] ![(33316382838807/100000000000000 : ℝ), (6409931148577/20000000000000 : ℝ), (34633961403543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547441809/1250000000 : ℝ)|^8231 ≤ (33316382838807/100000000000000 : ℝ)^6183
        have hw : |(547441809/1250000000 : ℝ)|=(547441809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1063462451/2500000000 : ℝ)|^8231 ≤ (6409931148577/20000000000000 : ℝ)^6183
        have hw : |(1063462451/2500000000 : ℝ)|=(1063462451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90180189/200000000 : ℝ)|^8231 ≤ (34633961403543/100000000000000 : ℝ)^6183
        have hw : |(90180189/200000000 : ℝ)|=(90180189/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217634257/10000000000 : ℝ)*x 0 + (2632126211/5000000000 : ℝ)*x 1 + (2697258051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217634257/10000000000 : ℝ)^8231 ≤ (6732843588713/50000000000000 : ℝ)^6183 := by
    have hnat : (2217634257 : ℕ)^8231*50000000000000^6183 ≤ 6732843588713^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217634257 10000000000 6732843588713 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632126211/5000000000 : ℝ)^8231 ≤ (21281627909367/50000000000000 : ℝ)^6183 := by
    have hnat : (2632126211 : ℕ)^8231*50000000000000^6183 ≤ 21281627909367^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632126211 5000000000 21281627909367 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697258051/5000000000 : ℝ)^8231 ≤ (43971056984739/100000000000000 : ℝ)^6183 := by
    have hnat : (2697258051 : ℕ)^8231*100000000000000^6183 ≤ 43971056984739^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697258051 5000000000 43971056984739 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217634257/10000000000 : ℝ), (2632126211/5000000000 : ℝ), (2697258051/5000000000 : ℝ)] ![(6732843588713/50000000000000 : ℝ), (21281627909367/50000000000000 : ℝ), (43971056984739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217634257/10000000000 : ℝ)|^8231 ≤ (6732843588713/50000000000000 : ℝ)^6183
        have hw : |(-2217634257/10000000000 : ℝ)|=(2217634257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632126211/5000000000 : ℝ)|^8231 ≤ (21281627909367/50000000000000 : ℝ)^6183
        have hw : |(2632126211/5000000000 : ℝ)|=(2632126211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697258051/5000000000 : ℝ)|^8231 ≤ (43971056984739/100000000000000 : ℝ)^6183
        have hw : |(2697258051/5000000000 : ℝ)|=(2697258051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312135263/10000000000 : ℝ)*x 0 + (-1076735153/5000000000 : ℝ)*x 1 + (5394516049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312135263/10000000000 : ℝ)^8231 ≤ (2153970759453/5000000000000 : ℝ)^6183 := by
    have hnat : (5312135263 : ℕ)^8231*5000000000000^6183 ≤ 2153970759453^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312135263 10000000000 2153970759453 5000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076735153/5000000000 : ℝ)^8231 ≤ (1294952838419/10000000000000 : ℝ)^6183 := by
    have hnat : (1076735153 : ℕ)^8231*10000000000000^6183 ≤ 1294952838419^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076735153 5000000000 1294952838419 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394516049/10000000000 : ℝ)^8231 ≤ (43971056409639/100000000000000 : ℝ)^6183 := by
    have hnat : (5394516049 : ℕ)^8231*100000000000000^6183 ≤ 43971056409639^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394516049 10000000000 43971056409639 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312135263/10000000000 : ℝ), (-1076735153/5000000000 : ℝ), (5394516049/10000000000 : ℝ)] ![(2153970759453/5000000000000 : ℝ), (1294952838419/10000000000000 : ℝ), (43971056409639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312135263/10000000000 : ℝ)|^8231 ≤ (2153970759453/5000000000000 : ℝ)^6183
        have hw : |(5312135263/10000000000 : ℝ)|=(5312135263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076735153/5000000000 : ℝ)|^8231 ≤ (1294952838419/10000000000000 : ℝ)^6183
        have hw : |(-1076735153/5000000000 : ℝ)|=(1076735153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394516049/10000000000 : ℝ)|^8231 ≤ (43971056409639/100000000000000 : ℝ)^6183
        have hw : |(5394516049/10000000000 : ℝ)|=(5394516049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062427047/2000000000 : ℝ)*x 0 + (1078903207/2000000000 : ℝ)*x 1 + (-538367591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062427047/2000000000 : ℝ)^8231 ≤ (21539707443389/50000000000000 : ℝ)^6183 := by
    have hnat : (1062427047 : ℕ)^8231*50000000000000^6183 ≤ 21539707443389^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062427047 2000000000 21539707443389 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078903207/2000000000 : ℝ)^8231 ≤ (21985528128863/50000000000000 : ℝ)^6183 := by
    have hnat : (1078903207 : ℕ)^8231*50000000000000^6183 ≤ 21985528128863^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078903207 2000000000 21985528128863 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538367591/2500000000 : ℝ)^8231 ≤ (1618691106061/12500000000000 : ℝ)^6183 := by
    have hnat : (538367591 : ℕ)^8231*12500000000000^6183 ≤ 1618691106061^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538367591 2500000000 1618691106061 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062427047/2000000000 : ℝ), (1078903207/2000000000 : ℝ), (-538367591/2500000000 : ℝ)] ![(21539707443389/50000000000000 : ℝ), (21985528128863/50000000000000 : ℝ), (1618691106061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062427047/2000000000 : ℝ)|^8231 ≤ (21539707443389/50000000000000 : ℝ)^6183
        have hw : |(1062427047/2000000000 : ℝ)|=(1062427047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078903207/2000000000 : ℝ)|^8231 ≤ (21985528128863/50000000000000 : ℝ)^6183
        have hw : |(1078903207/2000000000 : ℝ)|=(1078903207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538367591/2500000000 : ℝ)|^8231 ≤ (1618691106061/12500000000000 : ℝ)^6183
        have hw : |(-538367591/2500000000 : ℝ)|=(538367591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s8_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379544291/10000000000 : ℝ)*x 0 + (4508371043/10000000000 : ℝ)*x 1 + (4254490703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379544291/10000000000 : ℝ)^8231 ≤ (6663296455283/20000000000000 : ℝ)^6183 := by
    have hnat : (4379544291 : ℕ)^8231*20000000000000^6183 ≤ 6663296455283^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379544291 10000000000 6663296455283 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508371043/10000000000 : ℝ)^8231 ≤ (34627433678777/100000000000000 : ℝ)^6183 := by
    have hnat : (4508371043 : ℕ)^8231*100000000000000^6183 ≤ 34627433678777^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508371043 10000000000 34627433678777 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254490703/10000000000 : ℝ)^8231 ≤ (320560840261/1000000000000 : ℝ)^6183 := by
    have hnat : (4254490703 : ℕ)^8231*1000000000000^6183 ≤ 320560840261^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254490703 10000000000 320560840261 1000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379544291/10000000000 : ℝ), (4508371043/10000000000 : ℝ), (4254490703/10000000000 : ℝ)] ![(6663296455283/20000000000000 : ℝ), (34627433678777/100000000000000 : ℝ), (320560840261/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379544291/10000000000 : ℝ)|^8231 ≤ (6663296455283/20000000000000 : ℝ)^6183
        have hw : |(4379544291/10000000000 : ℝ)|=(4379544291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508371043/10000000000 : ℝ)|^8231 ≤ (34627433678777/100000000000000 : ℝ)^6183
        have hw : |(4508371043/10000000000 : ℝ)|=(4508371043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254490703/10000000000 : ℝ)|^8231 ≤ (320560840261/1000000000000 : ℝ)^6183
        have hw : |(4254490703/10000000000 : ℝ)|=(4254490703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2803/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2797/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1121/10000 : ℝ) ^ (4115/1024 : ℝ) ≤ (379077657449081/2500000000000000000 : ℝ) := by
    have hpowers : (1121/10000 : ℝ)^4115 ≤ (379077657449081/2500000000000000000 : ℝ)^1024 := by
      have hnat : (1121 : ℕ)^4115*2500000000000000000^1024 ≤ 379077657449081^1024*10000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1121 10000 379077657449081 2500000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1121/10000 : ℝ)) (X := (379077657449081/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3497/25000 : ℝ) ^ (4115/1024 : ℝ) ≤ (18456198881330939/50000000000000000000 : ℝ) := by
    have hpowers : (3497/25000 : ℝ)^4115 ≤ (18456198881330939/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3497 : ℕ)^4115*50000000000000000000^1024 ≤ 18456198881330939^1024*25000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3497 25000 18456198881330939 50000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3497/25000 : ℝ)) (X := (18456198881330939/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250379077657449081/1250000000000000000 : ℝ) ≤ (10000754568780579/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (1250379077657449081/1250000000000000000 : ℝ)^1024 ≤ (10000754568780579/10000000000000000 : ℝ)^4115 := by
      have hnat : (1250379077657449081 : ℕ)^1024*10000000000000000^4115 ≤ 10000754568780579^4115*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250379077657449081 1250000000000000000 10000754568780579 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000754568780579/10000000000000000 : ℝ)) (X := (1250379077657449081/1250000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026037752030312559/50000000000000000000 : ℝ) ≤ (5000647811540277/5000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50026037752030312559/50000000000000000000 : ℝ)^1024 ≤ (5000647811540277/5000000000000000 : ℝ)^4115 := by
      have hnat : (50026037752030312559 : ℕ)^1024*5000000000000000^4115 ≤ 5000647811540277^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026037752030312559 50000000000000000000 5000647811540277 5000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000647811540277/5000000000000000 : ℝ)) (X := (50026037752030312559/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018456198881330939/25000000000000000000 : ℝ) ≤ (10001836677380529/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (25018456198881330939/25000000000000000000 : ℝ)^1024 ≤ (10001836677380529/10000000000000000 : ℝ)^4115 := by
      have hnat : (25018456198881330939 : ℕ)^1024*10000000000000000^4115 ≤ 10001836677380529^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018456198881330939 25000000000000000000 10001836677380529 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001836677380529/10000000000000000 : ℝ)) (X := (25018456198881330939/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(379077657449081/2500000000000000000 : ℝ) ≤ ((4628327625777834827/4630000000000000000 : ℝ)+2*(7214057333/3704000000000 : ℝ)*(1121/10000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (4628327625777834827/4630000000000000000 : ℝ)+2*(7214057333/3704000000000 : ℝ)*(1121/10000 : ℝ)=(10000754568780579/10000000000000000 : ℝ) by norm_num, show 1+2*(379077657449081/2500000000000000000 : ℝ)=(1250379077657449081/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18456198881330939/50000000000000000000 : ℝ)+(379077657449081/2500000000000000000 : ℝ) ≤ ((4628327625777834827/4630000000000000000 : ℝ)+(7214057333/3704000000000 : ℝ)*((3497/25000 : ℝ)+(1121/10000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (4628327625777834827/4630000000000000000 : ℝ)+(7214057333/3704000000000 : ℝ)*((3497/25000 : ℝ)+(1121/10000 : ℝ))=(5000647811540277/5000000000000000 : ℝ) by norm_num, show 1+(18456198881330939/50000000000000000000 : ℝ)+(379077657449081/2500000000000000000 : ℝ)=(50026037752030312559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18456198881330939/50000000000000000000 : ℝ) ≤ ((4628327625777834827/4630000000000000000 : ℝ)+2*(7214057333/3704000000000 : ℝ)*(3497/25000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (4628327625777834827/4630000000000000000 : ℝ)+2*(7214057333/3704000000000 : ℝ)*(3497/25000 : ℝ)=(10001836677380529/10000000000000000 : ℝ) by norm_num, show 1+2*(18456198881330939/50000000000000000000 : ℝ)=(25018456198881330939/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4628327625777834827/4630000000000000000 : ℝ)*(X 1 0+X 2 0)+(7214057333/3704000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (4628327625777834827/4630000000000000000 : ℝ)) (alpha := (7214057333/3704000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4628327625777834827/4630000000000000000 : ℝ)*(X 0 1+X 2 1)+(7214057333/3704000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (4628327625777834827/4630000000000000000 : ℝ)) (alpha := (7214057333/3704000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4628327625777834827/4630000000000000000 : ℝ)*(X 0 2+X 1 2)+(7214057333/3704000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (4628327625777834827/4630000000000000000 : ℝ)) (alpha := (7214057333/3704000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-6930091/31250000 : ℝ)*X 0 0+(5394844887/10000000000 : ℝ)*X 0 1+(1052784963/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345037191/10000000000 : ℝ)*X 1 0+(-114203079/500000000 : ℝ)*X 1 1+(2631962403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345037197/10000000000 : ℝ)*X 2 0+(5263924809/10000000000 : ℝ)*X 2 1+(-17844231/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547441809/1250000000 : ℝ)*X 0 0+(1063462451/2500000000 : ℝ)*X 0 1+(90180189/200000000 : ℝ)*X 0 2+(547441809/1250000000 : ℝ)*X 1 0+(1063462451/2500000000 : ℝ)*X 1 1+(90180189/200000000 : ℝ)*X 1 2+(547441809/1250000000 : ℝ)*X 2 0+(1063462451/2500000000 : ℝ)*X 2 1+(90180189/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2217634257/10000000000 : ℝ)*X 0 0+(2632126211/5000000000 : ℝ)*X 0 1+(2697258051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312135263/10000000000 : ℝ)*X 1 0+(-1076735153/5000000000 : ℝ)*X 1 1+(5394516049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062427047/2000000000 : ℝ)*X 2 0+(1078903207/2000000000 : ℝ)*X 2 1+(-538367591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379544291/10000000000 : ℝ)*X 0 0+(4508371043/10000000000 : ℝ)*X 0 1+(4254490703/10000000000 : ℝ)*X 0 2+(4379544291/10000000000 : ℝ)*X 1 0+(4508371043/10000000000 : ℝ)*X 1 1+(4254490703/10000000000 : ℝ)*X 1 2+(4379544291/10000000000 : ℝ)*X 2 0+(4508371043/10000000000 : ℝ)*X 2 1+(4254490703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (950031624974963451685574391/115750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167887773/10000000000000 : ℝ)*(base19) + (153812237/10000000000000 : ℝ)*(base23) + (15963453/20000000000000 : ℝ)*(lower2) + (53003627/25000000000000 : ℝ)*(upper3) + (60428053/50000000000000 : ℝ)*(upper5) + (5778749742042111/100000000000000 : ℝ)*(major0) + (5778749742042111/100000000000000 : ℝ)*(major1) + (5778749742042111/100000000000000 : ℝ)*(major2) + (3819147058734841/50000000000000 : ℝ)*(sp0) + (954792070506899/12500000000000 : ℝ)*(sp1) + (7638336704810551/100000000000000 : ℝ)*(sp2) + (61236509289473/1562500000000 : ℝ)*(sp3) + (44125463239/100000000000000 : ℝ)*(sp4) + (24373037799/100000000000000 : ℝ)*(sp7) + (391916096756407/10000000000000 : ℝ)*(f.failure) + (3819169121466461/50000000000000 : ℝ)*(f.sum) + (261562931287/185200000000000000000000000 : ℝ)*base65 + (372841460040850203/463000000000000000000000000000000 : ℝ)*base68 + (605476026724850203/463000000000000000000000000000000 : ℝ)*base70 + (2569458716104850203/463000000000000000000000000000000 : ℝ)*base72 + (228412861901/185200000000000000000000000 : ℝ)*base73 + (8956773495596850203/463000000000000000000000000000000 : ℝ)*base76 + (2067761118229850203/463000000000000000000000000000000 : ℝ)*base78 + (4275248428238149797/463000000000000000000000000000000 : ℝ)*base79 + (2396824456361/926000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (556297/200000000000000000000 : ℝ)*base90 + (556297/200000000000000000000 : ℝ)*base92 + (556297/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55144888367721821430308931/14468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302289479/50000000000000 : ℝ)*(base19) + (599632861/100000000000000 : ℝ)*(base23) + (28555957/100000000000000 : ℝ)*(upper2) + (7488379/25000000000000 : ℝ)*(upper3) + (23289631/50000000000000 : ℝ)*(upper5) + (725974931560951/12500000000000 : ℝ)*(major0) + (725974931560951/12500000000000 : ℝ)*(major1) + (725974931560951/12500000000000 : ℝ)*(major2) + (7956033123/50000000000000 : ℝ)*(sp1) + (12967383233/100000000000000 : ℝ)*(sp2) + (1919184057983209/25000000000000 : ℝ)*(sp4) + (479794982205477/6250000000000 : ℝ)*(sp5) + (7676722664916741/100000000000000 : ℝ)*(sp6) + (984715636499679/25000000000000 : ℝ)*(sp7) + (984715636499679/25000000000000 : ℝ)*(f.failure) + (1919184057983209/25000000000000 : ℝ)*(f.sum) + (327501979827/115750000000000000000000000 : ℝ)*base65 + (87802688177709523/57875000000000000000000000000000 : ℝ)*base68 + (331997745367709523/57875000000000000000000000000000 : ℝ)*base70 + (126020038029459523/57875000000000000000000000000000 : ℝ)*base72 + (354272463231/57875000000000000000000000 : ℝ)*base74 + (223504053372209523/57875000000000000000000000000000 : ℝ)*base76 + (123660534702790477/57875000000000000000000000000000 : ℝ)*base77 + (296699065217709523/57875000000000000000000000000000 : ℝ)*base80 + (65614647399/23150000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2296991/500000000000000000000 : ℝ)*base89 + (2296991/500000000000000000000 : ℝ)*base91 + (2296991/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1038_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1038_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1038_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1038_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1038_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2803/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1038_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
