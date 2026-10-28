-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:19:29.703999+00:00
-- url     : https://prove2.me/submissions/7fcbf31c-1566-4390-b681-9afefc06ff94

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
theorem support_rectangle_w1242_s6_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529986387/2500000000 : ℝ)*x 0 + (1078277841/2000000000 : ℝ)*x 1 + (658379239/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529986387/2500000000 : ℝ)^8435 ≤ (12891689345943/100000000000000 : ℝ)^6387 := by
    have hnat : (529986387 : ℕ)^8435*100000000000000^6387 ≤ 12891689345943^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529986387 2500000000 12891689345943 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078277841/2000000000 : ℝ)^8435 ≤ (5528154438957/12500000000000 : ℝ)^6387 := by
    have hnat : (1078277841 : ℕ)^8435*12500000000000^6387 ≤ 5528154438957^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078277841 2000000000 5528154438957 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658379239/1250000000 : ℝ)^8435 ≤ (42883075125983/100000000000000 : ℝ)^6387 := by
    have hnat : (658379239 : ℕ)^8435*100000000000000^6387 ≤ 42883075125983^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658379239 1250000000 42883075125983 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529986387/2500000000 : ℝ), (1078277841/2000000000 : ℝ), (658379239/1250000000 : ℝ)] ![(12891689345943/100000000000000 : ℝ), (5528154438957/12500000000000 : ℝ), (42883075125983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529986387/2500000000 : ℝ)|^8435 ≤ (12891689345943/100000000000000 : ℝ)^6387
        have hw : |(-529986387/2500000000 : ℝ)|=(529986387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078277841/2000000000 : ℝ)|^8435 ≤ (5528154438957/12500000000000 : ℝ)^6387
        have hw : |(1078277841/2000000000 : ℝ)|=(1078277841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658379239/1250000000 : ℝ)|^8435 ≤ (42883075125983/100000000000000 : ℝ)^6387
        have hw : |(658379239/1250000000 : ℝ)|=(658379239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672178841/5000000000 : ℝ)*x 0 + (-1091499657/5000000000 : ℝ)*x 1 + (263351701/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672178841/5000000000 : ℝ)^8435 ≤ (8743289317053/20000000000000 : ℝ)^6387 := by
    have hnat : (2672178841 : ℕ)^8435*20000000000000^6387 ≤ 8743289317053^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672178841 5000000000 8743289317053 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091499657/5000000000 : ℝ)^8435 ≤ (3350119278689/25000000000000 : ℝ)^6387 := by
    have hnat : (1091499657 : ℕ)^8435*25000000000000^6387 ≤ 3350119278689^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091499657 5000000000 3350119278689 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263351701/500000000 : ℝ)^8435 ≤ (42883076287249/100000000000000 : ℝ)^6387 := by
    have hnat : (263351701 : ℕ)^8435*100000000000000^6387 ≤ 42883076287249^6387*500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263351701 500000000 42883076287249 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672178841/5000000000 : ℝ), (-1091499657/5000000000 : ℝ), (263351701/500000000 : ℝ)] ![(8743289317053/20000000000000 : ℝ), (3350119278689/25000000000000 : ℝ), (42883076287249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672178841/5000000000 : ℝ)|^8435 ≤ (8743289317053/20000000000000 : ℝ)^6387
        have hw : |(2672178841/5000000000 : ℝ)|=(2672178841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091499657/5000000000 : ℝ)|^8435 ≤ (3350119278689/25000000000000 : ℝ)^6387
        have hw : |(-1091499657/5000000000 : ℝ)|=(1091499657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263351701/500000000 : ℝ)|^8435 ≤ (42883076287249/100000000000000 : ℝ)^6387
        have hw : |(263351701/500000000 : ℝ)|=(263351701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344357489/10000000000 : ℝ)*x 0 + (5267034031/10000000000 : ℝ)*x 1 + (-2182999557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344357489/10000000000 : ℝ)^8435 ≤ (43716444500319/100000000000000 : ℝ)^6387 := by
    have hnat : (5344357489 : ℕ)^8435*100000000000000^6387 ≤ 43716444500319^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344357489 10000000000 43716444500319 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267034031/10000000000 : ℝ)^8435 ≤ (42883076405527/100000000000000 : ℝ)^6387 := by
    have hnat : (5267034031 : ℕ)^8435*100000000000000^6387 ≤ 42883076405527^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267034031 10000000000 42883076405527 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182999557/10000000000 : ℝ)^8435 ≤ (3350119771183/25000000000000 : ℝ)^6387 := by
    have hnat : (2182999557 : ℕ)^8435*25000000000000^6387 ≤ 3350119771183^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182999557 10000000000 3350119771183 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344357489/10000000000 : ℝ), (5267034031/10000000000 : ℝ), (-2182999557/10000000000 : ℝ)] ![(43716444500319/100000000000000 : ℝ), (42883076405527/100000000000000 : ℝ), (3350119771183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344357489/10000000000 : ℝ)|^8435 ≤ (43716444500319/100000000000000 : ℝ)^6387
        have hw : |(5344357489/10000000000 : ℝ)|=(5344357489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267034031/10000000000 : ℝ)|^8435 ≤ (42883076405527/100000000000000 : ℝ)^6387
        have hw : |(5267034031/10000000000 : ℝ)|=(5267034031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182999557/10000000000 : ℝ)|^8435 ≤ (3350119771183/25000000000000 : ℝ)^6387
        have hw : |(-2182999557/10000000000 : ℝ)|=(2182999557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870152677/2000000000 : ℝ)*x 0 + (2113204941/5000000000 : ℝ)*x 1 + (447867309/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870152677/2000000000 : ℝ)^8435 ≤ (33317392345939/100000000000000 : ℝ)^6387 := by
    have hnat : (870152677 : ℕ)^8435*100000000000000^6387 ≤ 33317392345939^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870152677 2000000000 33317392345939 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113204941/5000000000 : ℝ)^8435 ≤ (32065566431189/100000000000000 : ℝ)^6387 := by
    have hnat : (2113204941 : ℕ)^8435*100000000000000^6387 ≤ 32065566431189^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113204941 5000000000 32065566431189 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447867309/1000000000 : ℝ)^8435 ≤ (8654260303627/25000000000000 : ℝ)^6387 := by
    have hnat : (447867309 : ℕ)^8435*25000000000000^6387 ≤ 8654260303627^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447867309 1000000000 8654260303627 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870152677/2000000000 : ℝ), (2113204941/5000000000 : ℝ), (447867309/1000000000 : ℝ)] ![(33317392345939/100000000000000 : ℝ), (32065566431189/100000000000000 : ℝ), (8654260303627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870152677/2000000000 : ℝ)|^8435 ≤ (33317392345939/100000000000000 : ℝ)^6387
        have hw : |(870152677/2000000000 : ℝ)|=(870152677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113204941/5000000000 : ℝ)|^8435 ≤ (32065566431189/100000000000000 : ℝ)^6387
        have hw : |(2113204941/5000000000 : ℝ)|=(2113204941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447867309/1000000000 : ℝ)|^8435 ≤ (8654260303627/25000000000000 : ℝ)^6387
        have hw : |(447867309/1000000000 : ℝ)|=(447867309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059974969/5000000000 : ℝ)*x 0 + (5267348413/10000000000 : ℝ)*x 1 + (1347768447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059974969/5000000000 : ℝ)^8435 ≤ (6445862301171/50000000000000 : ℝ)^6387 := by
    have hnat : (1059974969 : ℕ)^8435*50000000000000^6387 ≤ 6445862301171^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059974969 5000000000 6445862301171 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267348413/10000000000 : ℝ)^8435 ≤ (134020177559/312500000000 : ℝ)^6387 := by
    have hnat : (5267348413 : ℕ)^8435*312500000000^6387 ≤ 134020177559^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267348413 10000000000 134020177559 312500000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347768447/2500000000 : ℝ)^8435 ≤ (690965915021/1562500000000 : ℝ)^6387 := by
    have hnat : (1347768447 : ℕ)^8435*1562500000000^6387 ≤ 690965915021^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347768447 2500000000 690965915021 1562500000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059974969/5000000000 : ℝ), (5267348413/10000000000 : ℝ), (1347768447/2500000000 : ℝ)] ![(6445862301171/50000000000000 : ℝ), (134020177559/312500000000 : ℝ), (690965915021/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059974969/5000000000 : ℝ)|^8435 ≤ (6445862301171/50000000000000 : ℝ)^6387
        have hw : |(-1059974969/5000000000 : ℝ)|=(1059974969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267348413/10000000000 : ℝ)|^8435 ≤ (134020177559/312500000000 : ℝ)^6387
        have hw : |(5267348413/10000000000 : ℝ)|=(5267348413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347768447/2500000000 : ℝ)|^8435 ≤ (690965915021/1562500000000 : ℝ)^6387
        have hw : |(1347768447/2500000000 : ℝ)|=(1347768447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53126277/100000000 : ℝ)*x 0 + (-2058960331/10000000000 : ℝ)*x 1 + (2695536661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53126277/100000000 : ℝ)^8435 ≤ (10843499931457/25000000000000 : ℝ)^6387 := by
    have hnat : (53126277 : ℕ)^8435*25000000000000^6387 ≤ 10843499931457^6387*100000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53126277 100000000 10843499931457 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058960331/10000000000 : ℝ)^8435 ≤ (6202093372147/50000000000000 : ℝ)^6387 := by
    have hnat : (2058960331 : ℕ)^8435*50000000000000^6387 ≤ 6202093372147^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058960331 10000000000 6202093372147 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695536661/5000000000 : ℝ)^8435 ≤ (44221813513157/100000000000000 : ℝ)^6387 := by
    have hnat : (2695536661 : ℕ)^8435*100000000000000^6387 ≤ 44221813513157^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695536661 5000000000 44221813513157 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53126277/100000000 : ℝ), (-2058960331/10000000000 : ℝ), (2695536661/5000000000 : ℝ)] ![(10843499931457/25000000000000 : ℝ), (6202093372147/50000000000000 : ℝ), (44221813513157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53126277/100000000 : ℝ)|^8435 ≤ (10843499931457/25000000000000 : ℝ)^6387
        have hw : |(53126277/100000000 : ℝ)|=(53126277/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058960331/10000000000 : ℝ)|^8435 ≤ (6202093372147/50000000000000 : ℝ)^6387
        have hw : |(-2058960331/10000000000 : ℝ)|=(2058960331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695536661/5000000000 : ℝ)|^8435 ≤ (44221813513157/100000000000000 : ℝ)^6387
        have hw : |(2695536661/5000000000 : ℝ)|=(2695536661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531262801/1000000000 : ℝ)*x 0 + (673884153/1250000000 : ℝ)*x 1 + (-514740011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531262801/1000000000 : ℝ)^8435 ≤ (10843500767079/25000000000000 : ℝ)^6387 := by
    have hnat : (531262801 : ℕ)^8435*25000000000000^6387 ≤ 10843500767079^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531262801 1000000000 10843500767079 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673884153/1250000000 : ℝ)^8435 ≤ (22110906225761/50000000000000 : ℝ)^6387 := by
    have hnat : (673884153 : ℕ)^8435*50000000000000^6387 ≤ 22110906225761^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673884153 1250000000 22110906225761 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514740011/2500000000 : ℝ)^8435 ≤ (248083689217/2000000000000 : ℝ)^6387 := by
    have hnat : (514740011 : ℕ)^8435*2000000000000^6387 ≤ 248083689217^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514740011 2500000000 248083689217 2000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531262801/1000000000 : ℝ), (673884153/1250000000 : ℝ), (-514740011/2500000000 : ℝ)] ![(10843500767079/25000000000000 : ℝ), (22110906225761/50000000000000 : ℝ), (248083689217/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531262801/1000000000 : ℝ)|^8435 ≤ (10843500767079/25000000000000 : ℝ)^6387
        have hw : |(531262801/1000000000 : ℝ)|=(531262801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673884153/1250000000 : ℝ)|^8435 ≤ (22110906225761/50000000000000 : ℝ)^6387
        have hw : |(673884153/1250000000 : ℝ)|=(673884153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514740011/2500000000 : ℝ)|^8435 ≤ (248083689217/2000000000000 : ℝ)^6387
        have hw : |(-514740011/2500000000 : ℝ)|=(514740011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s6_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175386391/5000000000 : ℝ)*x 0 + (447803531/1000000000 : ℝ)*x 1 + (4227050113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175386391/5000000000 : ℝ)^8435 ≤ (33317487380831/100000000000000 : ℝ)^6387 := by
    have hnat : (2175386391 : ℕ)^8435*100000000000000^6387 ≤ 33317487380831^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175386391 5000000000 33317487380831 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447803531/1000000000 : ℝ)^8435 ≤ (34610531083429/100000000000000 : ℝ)^6387 := by
    have hnat : (447803531 : ℕ)^8435*100000000000000^6387 ≤ 34610531083429^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447803531 1000000000 34610531083429 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227050113/10000000000 : ℝ)^8435 ≤ (16035990760343/50000000000000 : ℝ)^6387 := by
    have hnat : (4227050113 : ℕ)^8435*50000000000000^6387 ≤ 16035990760343^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227050113 10000000000 16035990760343 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175386391/5000000000 : ℝ), (447803531/1000000000 : ℝ), (4227050113/10000000000 : ℝ)] ![(33317487380831/100000000000000 : ℝ), (34610531083429/100000000000000 : ℝ), (16035990760343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175386391/5000000000 : ℝ)|^8435 ≤ (33317487380831/100000000000000 : ℝ)^6387
        have hw : |(2175386391/5000000000 : ℝ)|=(2175386391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447803531/1000000000 : ℝ)|^8435 ≤ (34610531083429/100000000000000 : ℝ)^6387
        have hw : |(447803531/1000000000 : ℝ)|=(447803531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227050113/10000000000 : ℝ)|^8435 ≤ (16035990760343/50000000000000 : ℝ)^6387
        have hw : |(4227050113/10000000000 : ℝ)|=(4227050113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5737/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1413/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1413/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5727/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1413/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1413/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5727/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1413/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1413/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5727/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5727/50000 : ℝ) ^ (4217/1024 : ℝ) ≤ (6661948586453189/50000000000000000000 : ℝ) := by
    have hpowers : (5727/50000 : ℝ)^4217 ≤ (6661948586453189/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5727 : ℕ)^4217*50000000000000000000^1024 ≤ 6661948586453189^1024*50000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5727 50000 6661948586453189 50000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5727/50000 : ℝ)) (X := (6661948586453189/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1413/10000 : ℝ) ^ (4217/1024 : ℝ) ≤ (1265336348799359/4000000000000000000 : ℝ) := by
    have hpowers : (1413/10000 : ℝ)^4217 ≤ (1265336348799359/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1413 : ℕ)^4217*4000000000000000000^1024 ≤ 1265336348799359^1024*10000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1413 10000 1265336348799359 4000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1413/10000 : ℝ)) (X := (1265336348799359/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006661948586453189/25000000000000000000 : ℝ) ≤ (625040438387711/625000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (25006661948586453189/25000000000000000000 : ℝ)^1024 ≤ (625040438387711/625000000000000 : ℝ)^4217 := by
      have hnat : (25006661948586453189 : ℕ)^1024*625000000000000^4217 ≤ 625040438387711^4217*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006661948586453189 25000000000000000000 625040438387711 625000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625040438387711/625000000000000 : ℝ)) (X := (25006661948586453189/25000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044957305892890353/100000000000000000000 : ℝ) ≤ (5000545748729107/5000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (100044957305892890353/100000000000000000000 : ℝ)^1024 ≤ (5000545748729107/5000000000000000 : ℝ)^4217 := by
      have hnat : (100044957305892890353 : ℕ)^1024*5000000000000000^4217 ≤ 5000545748729107^4217*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044957305892890353 100000000000000000000 5000545748729107 5000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000545748729107/5000000000000000 : ℝ)) (X := (100044957305892890353/100000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001265336348799359/2000000000000000000 : ℝ) ≤ (2500383995178263/2500000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (2001265336348799359/2000000000000000000 : ℝ)^1024 ≤ (2500383995178263/2500000000000000 : ℝ)^4217 := by
      have hnat : (2001265336348799359 : ℕ)^1024*2500000000000000^4217 ≤ 2500383995178263^4217*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001265336348799359 2000000000000000000 2500383995178263 2500000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500383995178263/2500000000000000 : ℝ)) (X := (2001265336348799359/2000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6661948586453189/50000000000000000000 : ℝ) ≤ ((1114647882816933553/1115000000000000000 : ℝ)+2*(74080542473/44600000000000 : ℝ)*(5727/50000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (1114647882816933553/1115000000000000000 : ℝ)+2*(74080542473/44600000000000 : ℝ)*(5727/50000 : ℝ)=(625040438387711/625000000000000 : ℝ) by norm_num, show 1+2*(6661948586453189/50000000000000000000 : ℝ)=(25006661948586453189/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1265336348799359/4000000000000000000 : ℝ)+(6661948586453189/50000000000000000000 : ℝ) ≤ ((1114647882816933553/1115000000000000000 : ℝ)+(74080542473/44600000000000 : ℝ)*((1413/10000 : ℝ)+(5727/50000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (1114647882816933553/1115000000000000000 : ℝ)+(74080542473/44600000000000 : ℝ)*((1413/10000 : ℝ)+(5727/50000 : ℝ))=(5000545748729107/5000000000000000 : ℝ) by norm_num, show 1+(1265336348799359/4000000000000000000 : ℝ)+(6661948586453189/50000000000000000000 : ℝ)=(100044957305892890353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1265336348799359/4000000000000000000 : ℝ) ≤ ((1114647882816933553/1115000000000000000 : ℝ)+2*(74080542473/44600000000000 : ℝ)*(1413/10000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (1114647882816933553/1115000000000000000 : ℝ)+2*(74080542473/44600000000000 : ℝ)*(1413/10000 : ℝ)=(2500383995178263/2500000000000000 : ℝ) by norm_num, show 1+2*(1265336348799359/4000000000000000000 : ℝ)=(2001265336348799359/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1114647882816933553/1115000000000000000 : ℝ)*(X 1 0+X 2 0)+(74080542473/44600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (1413/10000 : ℝ)) (c := (1114647882816933553/1115000000000000000 : ℝ)) (alpha := (74080542473/44600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1114647882816933553/1115000000000000000 : ℝ)*(X 0 1+X 2 1)+(74080542473/44600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (1413/10000 : ℝ)) (c := (1114647882816933553/1115000000000000000 : ℝ)) (alpha := (74080542473/44600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1114647882816933553/1115000000000000000 : ℝ)*(X 0 2+X 1 2)+(74080542473/44600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5727/50000 : ℝ)) (hi := (1413/10000 : ℝ)) (c := (1114647882816933553/1115000000000000000 : ℝ)) (alpha := (74080542473/44600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529986387/2500000000 : ℝ)*X 0 0+(1078277841/2000000000 : ℝ)*X 0 1+(658379239/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672178841/5000000000 : ℝ)*X 1 0+(-1091499657/5000000000 : ℝ)*X 1 1+(263351701/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344357489/10000000000 : ℝ)*X 2 0+(5267034031/10000000000 : ℝ)*X 2 1+(-2182999557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870152677/2000000000 : ℝ)*X 0 0+(2113204941/5000000000 : ℝ)*X 0 1+(447867309/1000000000 : ℝ)*X 0 2+(870152677/2000000000 : ℝ)*X 1 0+(2113204941/5000000000 : ℝ)*X 1 1+(447867309/1000000000 : ℝ)*X 1 2+(870152677/2000000000 : ℝ)*X 2 0+(2113204941/5000000000 : ℝ)*X 2 1+(447867309/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059974969/5000000000 : ℝ)*X 0 0+(5267348413/10000000000 : ℝ)*X 0 1+(1347768447/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53126277/100000000 : ℝ)*X 1 0+(-2058960331/10000000000 : ℝ)*X 1 1+(2695536661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531262801/1000000000 : ℝ)*X 2 0+(673884153/1250000000 : ℝ)*X 2 1+(-514740011/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175386391/5000000000 : ℝ)*X 0 0+(447803531/1000000000 : ℝ)*X 0 1+(4227050113/10000000000 : ℝ)*X 0 2+(2175386391/5000000000 : ℝ)*X 1 0+(447803531/1000000000 : ℝ)*X 1 1+(4227050113/10000000000 : ℝ)*X 1 2+(2175386391/5000000000 : ℝ)*X 2 0+(447803531/1000000000 : ℝ)*X 2 1+(4227050113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (617270648123992329733528881/55750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (857008971/50000000000000 : ℝ)*(base19) + (139526153/10000000000000 : ℝ)*(base23) + (4023561/50000000000000 : ℝ)*(upper2) + (132041773/50000000000000 : ℝ)*(upper3) + (6002881349746647/100000000000000 : ℝ)*(major0) + (6002881349746647/100000000000000 : ℝ)*(major1) + (6002881349746647/100000000000000 : ℝ)*(major2) + (1005192890663991/12500000000000 : ℝ)*(sp0) + (2010398131063691/25000000000000 : ℝ)*(sp1) + (1608317106289719/20000000000000 : ℝ)*(sp2) + (495517370726523/12500000000000 : ℝ)*(sp3) + (51112960779/100000000000000 : ℝ)*(sp4) + (7311562581/100000000000000 : ℝ)*(sp6) + (29126337749/100000000000000 : ℝ)*(sp7) + (1982084046074967/50000000000000 : ℝ)*(f.failure) + (8041594238272707/100000000000000 : ℝ)*(f.sum) + (9800543817729/2230000000000000000000000000 : ℝ)*base66 + (940043864316821791/111500000000000000000000000000000 : ℝ)*base67 + (1035570715506821791/111500000000000000000000000000000 : ℝ)*base69 + (2242411010865321791/111500000000000000000000000000000 : ℝ)*base71 + (1041191530171/2230000000000000000000000000 : ℝ)*base73 + (584886813248821791/111500000000000000000000000000000 : ℝ)*base75 + (1229235629919821791/111500000000000000000000000000000 : ℝ)*base77 + (1748671230963821791/111500000000000000000000000000000 : ℝ)*base79 + (4886892011891/2230000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (34383609/5000000000000000000000 : ℝ)*base89 + (34383609/5000000000000000000000 : ℝ)*base91 + (34383609/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19273864014917428454362431/1742187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (298200291/50000000000000 : ℝ)*(base19) + (1078657009/100000000000000 : ℝ)*(base23) + (119415961/100000000000000 : ℝ)*(lower2) + (37490957/100000000000000 : ℝ)*(lower3) + (67890323/100000000000000 : ℝ)*(lower4) + (377085569183991/6250000000000 : ℝ)*(major0) + (377085569183991/6250000000000 : ℝ)*(major1) + (377085569183991/6250000000000 : ℝ)*(major2) + (5181714347/100000000000000 : ℝ)*(sp0) + (9009764951/50000000000000 : ℝ)*(sp2) + (8082431140784647/100000000000000 : ℝ)*(sp4) + (2020608931524603/25000000000000 : ℝ)*(sp5) + (8082417224312083/100000000000000 : ℝ)*(sp6) + (9960753806553/250000000000 : ℝ)*(sp7) + (9960753806553/250000000000 : ℝ)*(f.failure) + (4041218161249497/50000000000000 : ℝ)*(f.sum) + (492182043113/557500000000000000000000000 : ℝ)*base66 + (106747348004487523/6968750000000000000000000000000 : ℝ)*base67 + (158110850518800023/6968750000000000000000000000000 : ℝ)*base69 + (3233321315574977/6968750000000000000000000000000 : ℝ)*base72 + (1427056160681/278750000000000000000000000 : ℝ)*base73 + (144596378982175023/6968750000000000000000000000000 : ℝ)*base75 + (76048973144300023/6968750000000000000000000000000 : ℝ)*base77 + (140354693961237523/6968750000000000000000000000000 : ℝ)*base79 + (1642077826267/557500000000000000000000000 : ℝ)*base81 + (262569/25000000000000000000 : ℝ)*base90 + (262569/25000000000000000000 : ℝ)*base92 + (262569/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1242_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1242_s7_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66248821/312500000 : ℝ)*x 0 + (1347799057/2500000000 : ℝ)*x 1 + (2633607923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66248821/312500000 : ℝ)^8435 ≤ (3222955914423/25000000000000 : ℝ)^6387 := by
    have hnat : (66248821 : ℕ)^8435*25000000000000^6387 ≤ 3222955914423^6387*312500000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66248821 312500000 3222955914423 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347799057/2500000000 : ℝ)^8435 ≤ (5527893120123/12500000000000 : ℝ)^6387 := by
    have hnat : (1347799057 : ℕ)^8435*12500000000000^6387 ≤ 5527893120123^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347799057 2500000000 5527893120123 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633607923/5000000000 : ℝ)^8435 ≤ (5360628921939/12500000000000 : ℝ)^6387 := by
    have hnat : (2633607923 : ℕ)^8435*12500000000000^6387 ≤ 5360628921939^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633607923 5000000000 5360628921939 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66248821/312500000 : ℝ), (1347799057/2500000000 : ℝ), (2633607923/5000000000 : ℝ)] ![(3222955914423/25000000000000 : ℝ), (5527893120123/12500000000000 : ℝ), (5360628921939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66248821/312500000 : ℝ)|^8435 ≤ (3222955914423/25000000000000 : ℝ)^6387
        have hw : |(-66248821/312500000 : ℝ)|=(66248821/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347799057/2500000000 : ℝ)|^8435 ≤ (5527893120123/12500000000000 : ℝ)^6387
        have hw : |(1347799057/2500000000 : ℝ)|=(1347799057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633607923/5000000000 : ℝ)|^8435 ≤ (5360628921939/12500000000000 : ℝ)^6387
        have hw : |(2633607923/5000000000 : ℝ)|=(2633607923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672154323/5000000000 : ℝ)*x 0 + (-2182823441/10000000000 : ℝ)*x 1 + (1316803971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672154323/5000000000 : ℝ)^8435 ≤ (21857958429257/50000000000000 : ℝ)^6387 := by
    have hnat : (2672154323 : ℕ)^8435*50000000000000^6387 ≤ 21857958429257^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672154323 5000000000 21857958429257 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182823441/10000000000 : ℝ)^8435 ≤ (13399051348293/100000000000000 : ℝ)^6387 := by
    have hnat : (2182823441 : ℕ)^8435*100000000000000^6387 ≤ 13399051348293^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182823441 10000000000 13399051348293 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316803971/2500000000 : ℝ)^8435 ≤ (4288503178411/10000000000000 : ℝ)^6387 := by
    have hnat : (1316803971 : ℕ)^8435*10000000000000^6387 ≤ 4288503178411^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316803971 2500000000 4288503178411 10000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672154323/5000000000 : ℝ), (-2182823441/10000000000 : ℝ), (1316803971/2500000000 : ℝ)] ![(21857958429257/50000000000000 : ℝ), (13399051348293/100000000000000 : ℝ), (4288503178411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672154323/5000000000 : ℝ)|^8435 ≤ (21857958429257/50000000000000 : ℝ)^6387
        have hw : |(2672154323/5000000000 : ℝ)|=(2672154323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182823441/10000000000 : ℝ)|^8435 ≤ (13399051348293/100000000000000 : ℝ)^6387
        have hw : |(-2182823441/10000000000 : ℝ)|=(2182823441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316803971/2500000000 : ℝ)|^8435 ≤ (4288503178411/10000000000000 : ℝ)^6387
        have hw : |(1316803971/2500000000 : ℝ)|=(1316803971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672154341/5000000000 : ℝ)*x 0 + (5267215861/10000000000 : ℝ)*x 1 + (-2182823423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672154341/5000000000 : ℝ)^8435 ≤ (21857958623707/50000000000000 : ℝ)^6387 := by
    have hnat : (2672154341 : ℕ)^8435*50000000000000^6387 ≤ 21857958623707^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672154341 5000000000 21857958623707 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267215861/10000000000 : ℝ)^8435 ≤ (53606289421/125000000000 : ℝ)^6387 := by
    have hnat : (5267215861 : ℕ)^8435*125000000000^6387 ≤ 53606289421^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267215861 10000000000 53606289421 125000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182823423/10000000000 : ℝ)^8435 ≤ (3349762800593/25000000000000 : ℝ)^6387 := by
    have hnat : (2182823423 : ℕ)^8435*25000000000000^6387 ≤ 3349762800593^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182823423 10000000000 3349762800593 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672154341/5000000000 : ℝ), (5267215861/10000000000 : ℝ), (-2182823423/10000000000 : ℝ)] ![(21857958623707/50000000000000 : ℝ), (53606289421/125000000000 : ℝ), (3349762800593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672154341/5000000000 : ℝ)|^8435 ≤ (21857958623707/50000000000000 : ℝ)^6387
        have hw : |(2672154341/5000000000 : ℝ)|=(2672154341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267215861/10000000000 : ℝ)|^8435 ≤ (53606289421/125000000000 : ℝ)^6387
        have hw : |(5267215861/10000000000 : ℝ)|=(5267215861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182823423/10000000000 : ℝ)|^8435 ≤ (3349762800593/25000000000000 : ℝ)^6387
        have hw : |(-2182823423/10000000000 : ℝ)|=(2182823423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543846653/1250000000 : ℝ)*x 0 + (528348587/1250000000 : ℝ)*x 1 + (2239145747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543846653/1250000000 : ℝ)^8435 ≤ (33317491850921/100000000000000 : ℝ)^6387 := by
    have hnat : (543846653 : ℕ)^8435*100000000000000^6387 ≤ 33317491850921^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543846653 1250000000 33317491850921 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528348587/1250000000 : ℝ)^8435 ≤ (16034681047483/50000000000000 : ℝ)^6387 := by
    have hnat : (528348587 : ℕ)^8435*50000000000000^6387 ≤ 16034681047483^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528348587 1250000000 16034681047483 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239145747/5000000000 : ℝ)^8435 ≤ (34613146042563/100000000000000 : ℝ)^6387 := by
    have hnat : (2239145747 : ℕ)^8435*100000000000000^6387 ≤ 34613146042563^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239145747 5000000000 34613146042563 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543846653/1250000000 : ℝ), (528348587/1250000000 : ℝ), (2239145747/5000000000 : ℝ)] ![(33317491850921/100000000000000 : ℝ), (16034681047483/50000000000000 : ℝ), (34613146042563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543846653/1250000000 : ℝ)|^8435 ≤ (33317491850921/100000000000000 : ℝ)^6387
        have hw : |(543846653/1250000000 : ℝ)|=(543846653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528348587/1250000000 : ℝ)|^8435 ≤ (16034681047483/50000000000000 : ℝ)^6387
        have hw : |(528348587/1250000000 : ℝ)|=(528348587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239145747/5000000000 : ℝ)|^8435 ≤ (34613146042563/100000000000000 : ℝ)^6387
        have hw : |(2239145747/5000000000 : ℝ)|=(2239145747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119966961/10000000000 : ℝ)*x 0 + (210701139/400000000 : ℝ)*x 1 + (5390882439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119966961/10000000000 : ℝ)^8435 ≤ (6445930657739/50000000000000 : ℝ)^6387 := by
    have hnat : (2119966961 : ℕ)^8435*50000000000000^6387 ≤ 6445930657739^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119966961 10000000000 6445930657739 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210701139/400000000 : ℝ)^8435 ≤ (42888392976643/100000000000000 : ℝ)^6387 := by
    have hnat : (210701139 : ℕ)^8435*100000000000000^6387 ≤ 42888392976643^6387*400000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210701139 400000000 42888392976643 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390882439/10000000000 : ℝ)^8435 ≤ (11054936421461/25000000000000 : ℝ)^6387 := by
    have hnat : (5390882439 : ℕ)^8435*25000000000000^6387 ≤ 11054936421461^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390882439 10000000000 11054936421461 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119966961/10000000000 : ℝ), (210701139/400000000 : ℝ), (5390882439/10000000000 : ℝ)] ![(6445930657739/50000000000000 : ℝ), (42888392976643/100000000000000 : ℝ), (11054936421461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119966961/10000000000 : ℝ)|^8435 ≤ (6445930657739/50000000000000 : ℝ)^6387
        have hw : |(-2119966961/10000000000 : ℝ)|=(2119966961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210701139/400000000 : ℝ)|^8435 ≤ (42888392976643/100000000000000 : ℝ)^6387
        have hw : |(210701139/400000000 : ℝ)|=(210701139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390882439/10000000000 : ℝ)|^8435 ≤ (11054936421461/25000000000000 : ℝ)^6387
        have hw : |(5390882439/10000000000 : ℝ)|=(5390882439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531267453/1000000000 : ℝ)*x 0 + (-2059156889/10000000000 : ℝ)*x 1 + (5390882347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531267453/1000000000 : ℝ)^8435 ≤ (43374504657987/100000000000000 : ℝ)^6387 := by
    have hnat : (531267453 : ℕ)^8435*100000000000000^6387 ≤ 43374504657987^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531267453 1000000000 43374504657987 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059156889/10000000000 : ℝ)^8435 ≤ (2481150126611/20000000000000 : ℝ)^6387 := by
    have hnat : (2059156889 : ℕ)^8435*20000000000000^6387 ≤ 2481150126611^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059156889 10000000000 2481150126611 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390882347/10000000000 : ℝ)^8435 ≤ (44219744689217/100000000000000 : ℝ)^6387 := by
    have hnat : (5390882347 : ℕ)^8435*100000000000000^6387 ≤ 44219744689217^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390882347 10000000000 44219744689217 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531267453/1000000000 : ℝ), (-2059156889/10000000000 : ℝ), (5390882347/10000000000 : ℝ)] ![(43374504657987/100000000000000 : ℝ), (2481150126611/20000000000000 : ℝ), (44219744689217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531267453/1000000000 : ℝ)|^8435 ≤ (43374504657987/100000000000000 : ℝ)^6387
        have hw : |(531267453/1000000000 : ℝ)|=(531267453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059156889/10000000000 : ℝ)|^8435 ≤ (2481150126611/20000000000000 : ℝ)^6387
        have hw : |(-2059156889/10000000000 : ℝ)|=(2059156889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390882347/10000000000 : ℝ)|^8435 ≤ (44219744689217/100000000000000 : ℝ)^6387
        have hw : |(5390882347/10000000000 : ℝ)|=(5390882347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328168633/2500000000 : ℝ)*x 0 + (5390882351/10000000000 : ℝ)*x 1 + (-1029578441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328168633/2500000000 : ℝ)^8435 ≤ (338863317809/781250000000 : ℝ)^6387 := by
    have hnat : (1328168633 : ℕ)^8435*781250000000^6387 ≤ 338863317809^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328168633 2500000000 338863317809 781250000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390882351/10000000000 : ℝ)^8435 ≤ (44219744732549/100000000000000 : ℝ)^6387 := by
    have hnat : (5390882351 : ℕ)^8435*100000000000000^6387 ≤ 44219744732549^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390882351 10000000000 44219744732549 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029578441/5000000000 : ℝ)^8435 ≤ (155071882217/1250000000000 : ℝ)^6387 := by
    have hnat : (1029578441 : ℕ)^8435*1250000000000^6387 ≤ 155071882217^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029578441 5000000000 155071882217 1250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328168633/2500000000 : ℝ), (5390882351/10000000000 : ℝ), (-1029578441/5000000000 : ℝ)] ![(338863317809/781250000000 : ℝ), (44219744732549/100000000000000 : ℝ), (155071882217/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328168633/2500000000 : ℝ)|^8435 ≤ (338863317809/781250000000 : ℝ)^6387
        have hw : |(1328168633/2500000000 : ℝ)|=(1328168633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390882351/10000000000 : ℝ)|^8435 ≤ (44219744732549/100000000000000 : ℝ)^6387
        have hw : |(5390882351/10000000000 : ℝ)|=(5390882351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029578441/5000000000 : ℝ)|^8435 ≤ (155071882217/1250000000000 : ℝ)^6387
        have hw : |(-1029578441/5000000000 : ℝ)|=(1029578441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s7_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870156531/2000000000 : ℝ)*x 0 + (34981697/78125000 : ℝ)*x 1 + (4227425289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870156531/2000000000 : ℝ)^8435 ≤ (4164698403717/12500000000000 : ℝ)^6387 := by
    have hnat : (870156531 : ℕ)^8435*12500000000000^6387 ≤ 4164698403717^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870156531 2000000000 4164698403717 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34981697/78125000 : ℝ)^8435 ≤ (34606671834193/100000000000000 : ℝ)^6387 := by
    have hnat : (34981697 : ℕ)^8435*100000000000000^6387 ≤ 34606671834193^6387*78125000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34981697 78125000 34606671834193 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227425289/10000000000 : ℝ)^8435 ≤ (32075740914269/100000000000000 : ℝ)^6387 := by
    have hnat : (4227425289 : ℕ)^8435*100000000000000^6387 ≤ 32075740914269^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227425289 10000000000 32075740914269 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870156531/2000000000 : ℝ), (34981697/78125000 : ℝ), (4227425289/10000000000 : ℝ)] ![(4164698403717/12500000000000 : ℝ), (34606671834193/100000000000000 : ℝ), (32075740914269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870156531/2000000000 : ℝ)|^8435 ≤ (4164698403717/12500000000000 : ℝ)^6387
        have hw : |(870156531/2000000000 : ℝ)|=(870156531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34981697/78125000 : ℝ)|^8435 ≤ (34606671834193/100000000000000 : ℝ)^6387
        have hw : |(34981697/78125000 : ℝ)|=(34981697/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227425289/10000000000 : ℝ)|^8435 ≤ (32075740914269/100000000000000 : ℝ)^6387
        have hw : |(4227425289/10000000000 : ℝ)|=(4227425289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5739/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5737/50000 : ℝ) ^ (4217/1024 : ℝ) ≤ (670998381723507/5000000000000000000 : ℝ) := by
    have hpowers : (5737/50000 : ℝ)^4217 ≤ (670998381723507/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5737 : ℕ)^4217*5000000000000000000^1024 ≤ 670998381723507^1024*50000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5737 50000 670998381723507 5000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5737/50000 : ℝ)) (X := (670998381723507/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (31440247315973327/100000000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^4217 ≤ (31440247315973327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14109 : ℕ)^4217*100000000000000000000^1024 ≤ 31440247315973327^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 31440247315973327 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (31440247315973327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500670998381723507/2500000000000000000 : ℝ) ≤ (10000651678952553/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (2500670998381723507/2500000000000000000 : ℝ)^1024 ≤ (10000651678952553/10000000000000000 : ℝ)^4217 := by
      have hnat : (2500670998381723507 : ℕ)^1024*10000000000000000^4217 ≤ 10000651678952553^4217*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500670998381723507 2500000000000000000 10000651678952553 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000651678952553/10000000000000000 : ℝ)) (X := (2500670998381723507/2500000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044860214950443467/100000000000000000000 : ℝ) ≤ (10001089140632709/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (100044860214950443467/100000000000000000000 : ℝ)^1024 ≤ (10001089140632709/10000000000000000 : ℝ)^4217 := by
      have hnat : (100044860214950443467 : ℕ)^1024*10000000000000000^4217 ≤ 10001089140632709^4217*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044860214950443467 100000000000000000000 10001089140632709 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089140632709/10000000000000000 : ℝ)) (X := (100044860214950443467/100000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031440247315973327/50000000000000000000 : ℝ) ≤ (2000305320462573/2000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50031440247315973327/50000000000000000000 : ℝ)^1024 ≤ (2000305320462573/2000000000000000 : ℝ)^4217 := by
      have hnat : (50031440247315973327 : ℕ)^1024*2000000000000000^4217 ≤ 2000305320462573^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031440247315973327 50000000000000000000 2000305320462573 2000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000305320462573/2000000000000000 : ℝ)) (X := (50031440247315973327/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(670998381723507/5000000000000000000 : ℝ) ≤ ((26341678303403757267/26350000000000000000 : ℝ)+2*(109365420039/65875000000000 : ℝ)*(5737/50000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (26341678303403757267/26350000000000000000 : ℝ)+2*(109365420039/65875000000000 : ℝ)*(5737/50000 : ℝ)=(10000651678952553/10000000000000000 : ℝ) by norm_num, show 1+2*(670998381723507/5000000000000000000 : ℝ)=(2500670998381723507/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31440247315973327/100000000000000000000 : ℝ)+(670998381723507/5000000000000000000 : ℝ) ≤ ((26341678303403757267/26350000000000000000 : ℝ)+(109365420039/65875000000000 : ℝ)*((14109/100000 : ℝ)+(5737/50000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (26341678303403757267/26350000000000000000 : ℝ)+(109365420039/65875000000000 : ℝ)*((14109/100000 : ℝ)+(5737/50000 : ℝ))=(10001089140632709/10000000000000000 : ℝ) by norm_num, show 1+(31440247315973327/100000000000000000000 : ℝ)+(670998381723507/5000000000000000000 : ℝ)=(100044860214950443467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31440247315973327/100000000000000000000 : ℝ) ≤ ((26341678303403757267/26350000000000000000 : ℝ)+2*(109365420039/65875000000000 : ℝ)*(14109/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (26341678303403757267/26350000000000000000 : ℝ)+2*(109365420039/65875000000000 : ℝ)*(14109/100000 : ℝ)=(2000305320462573/2000000000000000 : ℝ) by norm_num, show 1+2*(31440247315973327/100000000000000000000 : ℝ)=(50031440247315973327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26341678303403757267/26350000000000000000 : ℝ)*(X 1 0+X 2 0)+(109365420039/65875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5737/50000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (26341678303403757267/26350000000000000000 : ℝ)) (alpha := (109365420039/65875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26341678303403757267/26350000000000000000 : ℝ)*(X 0 1+X 2 1)+(109365420039/65875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5737/50000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (26341678303403757267/26350000000000000000 : ℝ)) (alpha := (109365420039/65875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26341678303403757267/26350000000000000000 : ℝ)*(X 0 2+X 1 2)+(109365420039/65875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5737/50000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (26341678303403757267/26350000000000000000 : ℝ)) (alpha := (109365420039/65875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66248821/312500000 : ℝ)*X 0 0+(1347799057/2500000000 : ℝ)*X 0 1+(2633607923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672154323/5000000000 : ℝ)*X 1 0+(-2182823441/10000000000 : ℝ)*X 1 1+(1316803971/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672154341/5000000000 : ℝ)*X 2 0+(5267215861/10000000000 : ℝ)*X 2 1+(-2182823423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543846653/1250000000 : ℝ)*X 0 0+(528348587/1250000000 : ℝ)*X 0 1+(2239145747/5000000000 : ℝ)*X 0 2+(543846653/1250000000 : ℝ)*X 1 0+(528348587/1250000000 : ℝ)*X 1 1+(2239145747/5000000000 : ℝ)*X 1 2+(543846653/1250000000 : ℝ)*X 2 0+(528348587/1250000000 : ℝ)*X 2 1+(2239145747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119966961/10000000000 : ℝ)*X 0 0+(210701139/400000000 : ℝ)*X 0 1+(5390882439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531267453/1000000000 : ℝ)*X 1 0+(-2059156889/10000000000 : ℝ)*X 1 1+(5390882347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328168633/2500000000 : ℝ)*X 2 0+(5390882351/10000000000 : ℝ)*X 2 1+(-1029578441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870156531/2000000000 : ℝ)*X 0 0+(34981697/78125000 : ℝ)*X 0 1+(4227425289/10000000000 : ℝ)*X 0 2+(870156531/2000000000 : ℝ)*X 1 0+(34981697/78125000 : ℝ)*X 1 1+(4227425289/10000000000 : ℝ)*X 1 2+(870156531/2000000000 : ℝ)*X 2 0+(34981697/78125000 : ℝ)*X 2 1+(4227425289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5686320484238494418060187249/658750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1701484733/100000000000000 : ℝ)*(base19) + (1640028943/100000000000000 : ℝ)*(base23) + (61881083/100000000000000 : ℝ)*(lower2) + (102988457/50000000000000 : ℝ)*(upper3) + (40016563/25000000000000 : ℝ)*(upper5) + (6021020324569049/100000000000000 : ℝ)*(major0) + (6021020324569049/100000000000000 : ℝ)*(major1) + (6021020324569049/100000000000000 : ℝ)*(major2) + (322633710324827/4000000000000 : ℝ)*(sp0) + (4032945997988579/50000000000000 : ℝ)*(sp1) + (8065892057432949/100000000000000 : ℝ)*(sp2) + (1988060893739841/50000000000000 : ℝ)*(sp3) + (1591854413/3125000000000 : ℝ)*(sp4) + (4975292733/20000000000000 : ℝ)*(sp7) + (1988073331971673/50000000000000 : ℝ)*(f.failure) + (8065893697461891/100000000000000 : ℝ)*(f.sum) + (5531587833581/13175000000000000000000000000 : ℝ)*base66 + (10202528781278570917/2635000000000000000000000000000000 : ℝ)*base68 + (30196645689703570917/2635000000000000000000000000000000 : ℝ)*base70 + (14285204629643570917/2635000000000000000000000000000000 : ℝ)*base72 + (444008494347/6587500000000000000000000000 : ℝ)*base73 + (73582155282566429083/2635000000000000000000000000000000 : ℝ)*base75 + (12323855949893570917/2635000000000000000000000000000000 : ℝ)*base78 + (35147716973293570917/2635000000000000000000000000000000 : ℝ)*base80 + (17528597308547/6587500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1884329/5000000000000000000000 : ℝ)*base90 + (1884329/5000000000000000000000 : ℝ)*base92 + (1884329/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53271829959204175649613/6587500000000000000000000000 : ℝ) := by norm_num
    linear_combination (365952941/20000000000000 : ℝ)*(base19) + (373543981/20000000000000 : ℝ)*(base23) + (66201149/50000000000000 : ℝ)*(upper3) + (12838351/50000000000000 : ℝ)*(lower4) + (116880037/50000000000000 : ℝ)*(upper5) + (47277526564881/781250000000 : ℝ)*(major0) + (47277526564881/781250000000 : ℝ)*(major1) + (47277526564881/781250000000 : ℝ)*(major2) + (51459029993/100000000000000 : ℝ)*(sp1) + (6150489431/12500000000000 : ℝ)*(sp2) + (810675632061577/10000000000000 : ℝ)*(sp4) + (8106703031821073/100000000000000 : ℝ)*(sp5) + (8106705248980417/100000000000000 : ℝ)*(sp6) + (1998145105216789/50000000000000 : ℝ)*(sp7) + (1998145105216789/50000000000000 : ℝ)*(f.failure) + (810675632061577/10000000000000 : ℝ)*(f.sum) + (556368791327/3293750000000000000000000000 : ℝ)*base65 + (18902643000993949/10292968750000000000000000000000 : ℝ)*base68 + (329893164826215227/20585937500000000000000000000000 : ℝ)*base69 + (116775872734943551/10292968750000000000000000000000 : ℝ)*base71 + (31022381320921/6587500000000000000000000000 : ℝ)*base74 + (77224986562491421/41171875000000000000000000000000 : ℝ)*base76 + (29593114166942287/5146484375000000000000000000000 : ℝ)*base78 + (1005176247385477329/41171875000000000000000000000000 : ℝ)*base79 + (3642926776769/411718750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (26060197/5000000000000000000000 : ℝ)*base90 + (26060197/5000000000000000000000 : ℝ)*base92 + (26060197/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1242_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1242_s8_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119964873/10000000000 : ℝ)*x 0 + (5391159093/10000000000 : ℝ)*x 1 + (1316812829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119964873/10000000000 : ℝ)^8435 ≤ (3222961136639/25000000000000 : ℝ)^6387 := by
    have hnat : (2119964873 : ℕ)^8435*25000000000000^6387 ≤ 3222961136639^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119964873 10000000000 3222961136639 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391159093/10000000000 : ℝ)^8435 ≤ (44222742674349/100000000000000 : ℝ)^6387 := by
    have hnat : (5391159093 : ℕ)^8435*100000000000000^6387 ≤ 44222742674349^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391159093 10000000000 44222742674349 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316812829/2500000000 : ℝ)^8435 ≤ (10721353192507/25000000000000 : ℝ)^6387 := by
    have hnat : (1316812829 : ℕ)^8435*25000000000000^6387 ≤ 10721353192507^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316812829 2500000000 10721353192507 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119964873/10000000000 : ℝ), (5391159093/10000000000 : ℝ), (1316812829/2500000000 : ℝ)] ![(3222961136639/25000000000000 : ℝ), (44222742674349/100000000000000 : ℝ), (10721353192507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119964873/10000000000 : ℝ)|^8435 ≤ (3222961136639/25000000000000 : ℝ)^6387
        have hw : |(-2119964873/10000000000 : ℝ)|=(2119964873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391159093/10000000000 : ℝ)|^8435 ≤ (44222742674349/100000000000000 : ℝ)^6387
        have hw : |(5391159093/10000000000 : ℝ)|=(5391159093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316812829/2500000000 : ℝ)|^8435 ≤ (10721353192507/25000000000000 : ℝ)^6387
        have hw : |(1316812829/2500000000 : ℝ)|=(1316812829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668037427/1250000000 : ℝ)*x 0 + (-2182788817/10000000000 : ℝ)*x 1 + (263362563/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668037427/1250000000 : ℝ)^8435 ≤ (43715817148721/100000000000000 : ℝ)^6387 := by
    have hnat : (668037427 : ℕ)^8435*100000000000000^6387 ≤ 43715817148721^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668037427 1250000000 43715817148721 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182788817/10000000000 : ℝ)^8435 ≤ (13398770662941/100000000000000 : ℝ)^6387 := by
    have hnat : (2182788817 : ℕ)^8435*100000000000000^6387 ≤ 13398770662941^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182788817 10000000000 13398770662941 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263362563/500000000 : ℝ)^8435 ≤ (21442706083941/50000000000000 : ℝ)^6387 := by
    have hnat : (263362563 : ℕ)^8435*50000000000000^6387 ≤ 21442706083941^6387*500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263362563 500000000 21442706083941 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668037427/1250000000 : ℝ), (-2182788817/10000000000 : ℝ), (263362563/500000000 : ℝ)] ![(43715817148721/100000000000000 : ℝ), (13398770662941/100000000000000 : ℝ), (21442706083941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668037427/1250000000 : ℝ)|^8435 ≤ (43715817148721/100000000000000 : ℝ)^6387
        have hw : |(668037427/1250000000 : ℝ)|=(668037427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182788817/10000000000 : ℝ)|^8435 ≤ (13398770662941/100000000000000 : ℝ)^6387
        have hw : |(-2182788817/10000000000 : ℝ)|=(2182788817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263362563/500000000 : ℝ)|^8435 ≤ (21442706083941/50000000000000 : ℝ)^6387
        have hw : |(263362563/500000000 : ℝ)|=(263362563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344299423/10000000000 : ℝ)*x 0 + (1316812817/2500000000 : ℝ)*x 1 + (-1091394399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344299423/10000000000 : ℝ)^8435 ≤ (43715817224341/100000000000000 : ℝ)^6387 := by
    have hnat : (5344299423 : ℕ)^8435*100000000000000^6387 ≤ 43715817224341^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344299423 10000000000 43715817224341 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316812817/2500000000 : ℝ)^8435 ≤ (42885412253903/100000000000000 : ℝ)^6387 := by
    have hnat : (1316812817 : ℕ)^8435*100000000000000^6387 ≤ 42885412253903^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316812817 2500000000 42885412253903 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091394399/5000000000 : ℝ)^8435 ≤ (2679754101783/20000000000000 : ℝ)^6387 := by
    have hnat : (1091394399 : ℕ)^8435*20000000000000^6387 ≤ 2679754101783^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091394399 5000000000 2679754101783 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344299423/10000000000 : ℝ), (1316812817/2500000000 : ℝ), (-1091394399/5000000000 : ℝ)] ![(43715817224341/100000000000000 : ℝ), (42885412253903/100000000000000 : ℝ), (2679754101783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344299423/10000000000 : ℝ)|^8435 ≤ (43715817224341/100000000000000 : ℝ)^6387
        have hw : |(5344299423/10000000000 : ℝ)|=(5344299423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316812817/2500000000 : ℝ)|^8435 ≤ (42885412253903/100000000000000 : ℝ)^6387
        have hw : |(1316812817/2500000000 : ℝ)|=(1316812817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091394399/5000000000 : ℝ)|^8435 ≤ (2679754101783/20000000000000 : ℝ)^6387
        have hw : |(-1091394399/5000000000 : ℝ)|=(1091394399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087693757/2500000000 : ℝ)*x 0 + (132089437/312500000 : ℝ)*x 1 + (4478217763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087693757/2500000000 : ℝ)^8435 ≤ (33317510095363/100000000000000 : ℝ)^6387 := by
    have hnat : (1087693757 : ℕ)^8435*100000000000000^6387 ≤ 33317510095363^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087693757 2500000000 33317510095363 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132089437/312500000 : ℝ)^8435 ≤ (16035048221581/50000000000000 : ℝ)^6387 := by
    have hnat : (132089437 : ℕ)^8435*50000000000000^6387 ≤ 16035048221581^6387*312500000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132089437 312500000 16035048221581 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478217763/10000000000 : ℝ)^8435 ≤ (17306196719851/50000000000000 : ℝ)^6387 := by
    have hnat : (4478217763 : ℕ)^8435*50000000000000^6387 ≤ 17306196719851^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478217763 10000000000 17306196719851 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087693757/2500000000 : ℝ), (132089437/312500000 : ℝ), (4478217763/10000000000 : ℝ)] ![(33317510095363/100000000000000 : ℝ), (16035048221581/50000000000000 : ℝ), (17306196719851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087693757/2500000000 : ℝ)|^8435 ≤ (33317510095363/100000000000000 : ℝ)^6387
        have hw : |(1087693757/2500000000 : ℝ)|=(1087693757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132089437/312500000 : ℝ)|^8435 ≤ (16035048221581/50000000000000 : ℝ)^6387
        have hw : |(132089437/312500000 : ℝ)|=(132089437/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478217763/10000000000 : ℝ)|^8435 ≤ (17306196719851/50000000000000 : ℝ)^6387
        have hw : |(4478217763/10000000000 : ℝ)|=(4478217763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059984771/5000000000 : ℝ)*x 0 + (2633781827/5000000000 : ℝ)*x 1 + (5390845607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059984771/5000000000 : ℝ)^8435 ≤ (2578376408747/20000000000000 : ℝ)^6387 := by
    have hnat : (1059984771 : ℕ)^8435*20000000000000^6387 ≤ 2578376408747^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059984771 5000000000 2578376408747 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633781827/5000000000 : ℝ)^8435 ≤ (857775424987/2000000000000 : ℝ)^6387 := by
    have hnat : (2633781827 : ℕ)^8435*2000000000000^6387 ≤ 857775424987^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633781827 5000000000 857775424987 2000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390845607/10000000000 : ℝ)^8435 ≤ (44219346689077/100000000000000 : ℝ)^6387 := by
    have hnat : (5390845607 : ℕ)^8435*100000000000000^6387 ≤ 44219346689077^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390845607 10000000000 44219346689077 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059984771/5000000000 : ℝ), (2633781827/5000000000 : ℝ), (5390845607/10000000000 : ℝ)] ![(2578376408747/20000000000000 : ℝ), (857775424987/2000000000000 : ℝ), (44219346689077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059984771/5000000000 : ℝ)|^8435 ≤ (2578376408747/20000000000000 : ℝ)^6387
        have hw : |(-1059984771/5000000000 : ℝ)|=(1059984771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633781827/5000000000 : ℝ)|^8435 ≤ (857775424987/2000000000000 : ℝ)^6387
        have hw : |(2633781827/5000000000 : ℝ)|=(2633781827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390845607/10000000000 : ℝ)|^8435 ≤ (44219346689077/100000000000000 : ℝ)^6387
        have hw : |(5390845607/10000000000 : ℝ)|=(5390845607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132817091/250000000 : ℝ)*x 0 + (-2059194373/10000000000 : ℝ)*x 1 + (5390845749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132817091/250000000 : ℝ)^8435 ≤ (43374602884333/100000000000000 : ℝ)^6387 := by
    have hnat : (132817091 : ℕ)^8435*100000000000000^6387 ≤ 43374602884333^6387*250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132817091 250000000 43374602884333 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059194373/10000000000 : ℝ)^8435 ≤ (496241955007/4000000000000 : ℝ)^6387 := by
    have hnat : (2059194373 : ℕ)^8435*4000000000000^6387 ≤ 496241955007^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059194373 10000000000 496241955007 4000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390845749/10000000000 : ℝ)^8435 ≤ (8843869645469/20000000000000 : ℝ)^6387 := by
    have hnat : (5390845749 : ℕ)^8435*20000000000000^6387 ≤ 8843869645469^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390845749 10000000000 8843869645469 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132817091/250000000 : ℝ), (-2059194373/10000000000 : ℝ), (5390845749/10000000000 : ℝ)] ![(43374602884333/100000000000000 : ℝ), (496241955007/4000000000000 : ℝ), (8843869645469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132817091/250000000 : ℝ)|^8435 ≤ (43374602884333/100000000000000 : ℝ)^6387
        have hw : |(132817091/250000000 : ℝ)|=(132817091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2059194373/10000000000 : ℝ)|^8435 ≤ (496241955007/4000000000000 : ℝ)^6387
        have hw : |(-2059194373/10000000000 : ℝ)|=(2059194373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390845749/10000000000 : ℝ)|^8435 ≤ (8843869645469/20000000000000 : ℝ)^6387
        have hw : |(5390845749/10000000000 : ℝ)|=(5390845749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312683713/10000000000 : ℝ)*x 0 + (1078169129/2000000000 : ℝ)*x 1 + (-411838883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312683713/10000000000 : ℝ)^8435 ≤ (43374603671437/100000000000000 : ℝ)^6387 := by
    have hnat : (5312683713 : ℕ)^8435*100000000000000^6387 ≤ 43374603671437^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312683713 10000000000 43374603671437 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078169129/2000000000 : ℝ)^8435 ≤ (22109673550363/50000000000000 : ℝ)^6387 := by
    have hnat : (1078169129 : ℕ)^8435*50000000000000^6387 ≤ 22109673550363^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078169129 2000000000 22109673550363 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411838883/2000000000 : ℝ)^8435 ≤ (248120984187/2000000000000 : ℝ)^6387 := by
    have hnat : (411838883 : ℕ)^8435*2000000000000^6387 ≤ 248120984187^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411838883 2000000000 248120984187 2000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312683713/10000000000 : ℝ), (1078169129/2000000000 : ℝ), (-411838883/2000000000 : ℝ)] ![(43374603671437/100000000000000 : ℝ), (22109673550363/50000000000000 : ℝ), (248120984187/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312683713/10000000000 : ℝ)|^8435 ≤ (43374603671437/100000000000000 : ℝ)^6387
        have hw : |(5312683713/10000000000 : ℝ)|=(5312683713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078169129/2000000000 : ℝ)|^8435 ≤ (22109673550363/50000000000000 : ℝ)^6387
        have hw : |(1078169129/2000000000 : ℝ)|=(1078169129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411838883/2000000000 : ℝ)|^8435 ≤ (248120984187/2000000000000 : ℝ)^6387
        have hw : |(-411838883/2000000000 : ℝ)|=(411838883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s8_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175392219/5000000000 : ℝ)*x 0 + (4477584297/10000000000 : ℝ)*x 1 + (4227497767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175392219/5000000000 : ℝ)^8435 ≤ (3331760526181/10000000000000 : ℝ)^6387 := by
    have hnat : (2175392219 : ℕ)^8435*10000000000000^6387 ≤ 3331760526181^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175392219 5000000000 3331760526181 10000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477584297/10000000000 : ℝ)^8435 ≤ (67589702253/195312500000 : ℝ)^6387 := by
    have hnat : (4477584297 : ℕ)^8435*195312500000^6387 ≤ 67589702253^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477584297 10000000000 67589702253 195312500000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227497767/10000000000 : ℝ)^8435 ≤ (6415293436257/20000000000000 : ℝ)^6387 := by
    have hnat : (4227497767 : ℕ)^8435*20000000000000^6387 ≤ 6415293436257^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227497767 10000000000 6415293436257 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175392219/5000000000 : ℝ), (4477584297/10000000000 : ℝ), (4227497767/10000000000 : ℝ)] ![(3331760526181/10000000000000 : ℝ), (67589702253/195312500000 : ℝ), (6415293436257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175392219/5000000000 : ℝ)|^8435 ≤ (3331760526181/10000000000000 : ℝ)^6387
        have hw : |(2175392219/5000000000 : ℝ)|=(2175392219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477584297/10000000000 : ℝ)|^8435 ≤ (67589702253/195312500000 : ℝ)^6387
        have hw : |(4477584297/10000000000 : ℝ)|=(4477584297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227497767/10000000000 : ℝ)|^8435 ≤ (6415293436257/20000000000000 : ℝ)^6387
        have hw : |(4227497767/10000000000 : ℝ)|=(4227497767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11479/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5739/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5739/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5739/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5739/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5739/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5739/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5739/50000 : ℝ) ^ (4217/1024 : ℝ) ≤ (13439244494746513/100000000000000000000 : ℝ) := by
    have hpowers : (5739/50000 : ℝ)^4217 ≤ (13439244494746513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5739 : ℕ)^4217*100000000000000000000^1024 ≤ 13439244494746513^1024*50000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5739 50000 13439244494746513 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5739/50000 : ℝ)) (X := (13439244494746513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (4217/1024 : ℝ) ≤ (31403556160468261/100000000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^4217 ≤ (31403556160468261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2821 : ℕ)^4217*100000000000000000000^1024 ≤ 31403556160468261^1024*20000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 31403556160468261 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (31403556160468261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013439244494746513/50000000000000000000 : ℝ) ≤ (10000652614949301/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50013439244494746513/50000000000000000000 : ℝ)^1024 ≤ (10000652614949301/10000000000000000 : ℝ)^4217 := by
      have hnat : (50013439244494746513 : ℕ)^1024*10000000000000000^4217 ≤ 10000652614949301^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013439244494746513 50000000000000000000 10000652614949301 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000652614949301/10000000000000000 : ℝ)) (X := (50013439244494746513/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022421400327607387/50000000000000000000 : ℝ) ≤ (2000217743582151/2000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50022421400327607387/50000000000000000000 : ℝ)^1024 ≤ (2000217743582151/2000000000000000 : ℝ)^4217 := by
      have hnat : (50022421400327607387 : ℕ)^1024*2000000000000000^4217 ≤ 2000217743582151^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022421400327607387 50000000000000000000 2000217743582151 2000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000217743582151/2000000000000000 : ℝ)) (X := (50022421400327607387/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031403556160468261/50000000000000000000 : ℝ) ≤ (10001524820872209/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50031403556160468261/50000000000000000000 : ℝ)^1024 ≤ (10001524820872209/10000000000000000 : ℝ)^4217 := by
      have hnat : (50031403556160468261 : ℕ)^1024*10000000000000000^4217 ≤ 10001524820872209^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031403556160468261 50000000000000000000 10001524820872209 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001524820872209/10000000000000000 : ℝ)) (X := (50031403556160468261/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13439244494746513/100000000000000000000 : ℝ) ≤ ((26261703239888675703/26270000000000000000 : ℝ)+2*(218051480727/131350000000000 : ℝ)*(5739/50000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (26261703239888675703/26270000000000000000 : ℝ)+2*(218051480727/131350000000000 : ℝ)*(5739/50000 : ℝ)=(10000652614949301/10000000000000000 : ℝ) by norm_num, show 1+2*(13439244494746513/100000000000000000000 : ℝ)=(50013439244494746513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31403556160468261/100000000000000000000 : ℝ)+(13439244494746513/100000000000000000000 : ℝ) ≤ ((26261703239888675703/26270000000000000000 : ℝ)+(218051480727/131350000000000 : ℝ)*((2821/20000 : ℝ)+(5739/50000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (26261703239888675703/26270000000000000000 : ℝ)+(218051480727/131350000000000 : ℝ)*((2821/20000 : ℝ)+(5739/50000 : ℝ))=(2000217743582151/2000000000000000 : ℝ) by norm_num, show 1+(31403556160468261/100000000000000000000 : ℝ)+(13439244494746513/100000000000000000000 : ℝ)=(50022421400327607387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31403556160468261/100000000000000000000 : ℝ) ≤ ((26261703239888675703/26270000000000000000 : ℝ)+2*(218051480727/131350000000000 : ℝ)*(2821/20000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (26261703239888675703/26270000000000000000 : ℝ)+2*(218051480727/131350000000000 : ℝ)*(2821/20000 : ℝ)=(10001524820872209/10000000000000000 : ℝ) by norm_num, show 1+2*(31403556160468261/100000000000000000000 : ℝ)=(50031403556160468261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26261703239888675703/26270000000000000000 : ℝ)*(X 1 0+X 2 0)+(218051480727/131350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (26261703239888675703/26270000000000000000 : ℝ)) (alpha := (218051480727/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26261703239888675703/26270000000000000000 : ℝ)*(X 0 1+X 2 1)+(218051480727/131350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (26261703239888675703/26270000000000000000 : ℝ)) (alpha := (218051480727/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26261703239888675703/26270000000000000000 : ℝ)*(X 0 2+X 1 2)+(218051480727/131350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (5739/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (26261703239888675703/26270000000000000000 : ℝ)) (alpha := (218051480727/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2119964873/10000000000 : ℝ)*X 0 0+(5391159093/10000000000 : ℝ)*X 0 1+(1316812829/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668037427/1250000000 : ℝ)*X 1 0+(-2182788817/10000000000 : ℝ)*X 1 1+(263362563/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344299423/10000000000 : ℝ)*X 2 0+(1316812817/2500000000 : ℝ)*X 2 1+(-1091394399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087693757/2500000000 : ℝ)*X 0 0+(132089437/312500000 : ℝ)*X 0 1+(4478217763/10000000000 : ℝ)*X 0 2+(1087693757/2500000000 : ℝ)*X 1 0+(132089437/312500000 : ℝ)*X 1 1+(4478217763/10000000000 : ℝ)*X 1 2+(1087693757/2500000000 : ℝ)*X 2 0+(132089437/312500000 : ℝ)*X 2 1+(4478217763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059984771/5000000000 : ℝ)*X 0 0+(2633781827/5000000000 : ℝ)*X 0 1+(5390845607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132817091/250000000 : ℝ)*X 1 0+(-2059194373/10000000000 : ℝ)*X 1 1+(5390845749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312683713/10000000000 : ℝ)*X 2 0+(1078169129/2000000000 : ℝ)*X 2 1+(-411838883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175392219/5000000000 : ℝ)*X 0 0+(4477584297/10000000000 : ℝ)*X 0 1+(4227497767/10000000000 : ℝ)*X 0 2+(2175392219/5000000000 : ℝ)*X 1 0+(4477584297/10000000000 : ℝ)*X 1 1+(4227497767/10000000000 : ℝ)*X 1 2+(2175392219/5000000000 : ℝ)*X 2 0+(4477584297/10000000000 : ℝ)*X 2 1+(4227497767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4227565530919187928155657127/656750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1249291539/100000000000000 : ℝ)*(base19) + (567545711/50000000000000 : ℝ)*(base23) + (8335171/12500000000000 : ℝ)*(lower2) + (147226357/100000000000000 : ℝ)*(upper3) + (17912293/20000000000000 : ℝ)*(upper5) + (6024521210943797/100000000000000 : ℝ)*(major0) + (6024521210943797/100000000000000 : ℝ)*(major1) + (6024521210943797/100000000000000 : ℝ)*(major2) + (4035275683384849/50000000000000 : ℝ)*(sp0) + (8070582387307853/100000000000000 : ℝ)*(sp1) + (807058250150797/10000000000000 : ℝ)*(sp2) + (3978440554732719/100000000000000 : ℝ)*(sp3) + (6453965939/20000000000000 : ℝ)*(sp4) + (2251998183/12500000000000 : ℝ)*(sp7) + (1989229285359091/50000000000000 : ℝ)*(f.failure) + (252205738643731/3125000000000 : ℝ)*(f.sum) + (22902869186181/6567500000000000000000000000 : ℝ)*base66 + (20918096134180264291/2627000000000000000000000000000000 : ℝ)*base67 + (9618617365590264291/2627000000000000000000000000000000 : ℝ)*base69 + (14000728428252264291/2627000000000000000000000000000000 : ℝ)*base71 + (54564827347567/13135000000000000000000000000 : ℝ)*base74 + (71789666060021264291/2627000000000000000000000000000000 : ℝ)*base75 + (28296040234421735709/2627000000000000000000000000000000 : ℝ)*base78 + (75209946506648264291/2627000000000000000000000000000000 : ℝ)*base79 + (14527991308463/13135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (33811043/5000000000000000000000 : ℝ)*base90 + (33811043/5000000000000000000000 : ℝ)*base92 + (33811043/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (890417914765438116312832551/131350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1103551747/100000000000000 : ℝ)*(base19) + (667175217/50000000000000 : ℝ)*(base23) + (8530623/2000000000000 : ℝ)*(lower1) + (197295399/100000000000000 : ℝ)*(upper3) + (22326491/50000000000000 : ℝ)*(lower4) + (193643/312500000000 : ℝ)*(upper5) + (1211004810411739/20000000000000 : ℝ)*(major0) + (1211004810411739/20000000000000 : ℝ)*(major1) + (1211004810411739/20000000000000 : ℝ)*(major2) + (5930433387/100000000000000 : ℝ)*(sp2) + (126741342435649/1562500000000 : ℝ)*(sp4) + (8111444812329789/100000000000000 : ℝ)*(sp5) + (8111438651097717/100000000000000 : ℝ)*(sp6) + (999650490567523/25000000000000 : ℝ)*(sp7) + (999650490567523/25000000000000 : ℝ)*(f.failure) + (126741342435649/1562500000000 : ℝ)*(f.sum) + (9260488664031/1313500000000000000000000000 : ℝ)*base66 + (13819972410121322483/525400000000000000000000000000000 : ℝ)*base68 + (2050911986059477517/525400000000000000000000000000000 : ℝ)*base69 + (141584454920776522483/525400000000000000000000000000000 : ℝ)*base72 + (15517308198423/2627000000000000000000000000 : ℝ)*base74 + (27339283415509122483/525400000000000000000000000000000 : ℝ)*base76 + (4274562662611322483/525400000000000000000000000000000 : ℝ)*base78 + (13410625198401122483/525400000000000000000000000000000 : ℝ)*base80 + (1739295823447/525400000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base87 + (26928621/2500000000000000000000 : ℝ)*base89 + (26928621/2500000000000000000000 : ℝ)*base91 + (26928621/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1242_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5739/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1242_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1242_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1242_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1242_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
