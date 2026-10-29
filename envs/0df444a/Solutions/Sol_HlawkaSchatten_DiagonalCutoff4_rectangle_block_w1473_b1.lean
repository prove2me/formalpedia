-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1473_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:01.421386+00:00
-- url     : https://prove2.me/submissions/72c13339-b857-49d9-9bf4-1a65e3783706

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
theorem support_rectangle_w1473_s3_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1926419961/10000000000 : ℝ)*x 0 + (272172521/500000000 : ℝ)*x 1 + (208433391/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926419961/10000000000 : ℝ)^4443 ≤ (11763373800389/100000000000000 : ℝ)^3419 := by
    have hnat : (1926419961 : ℕ)^4443*100000000000000^3419 ≤ 11763373800389^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926419961 10000000000 11763373800389 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272172521/500000000 : ℝ)^4443 ≤ (45369906274063/100000000000000 : ℝ)^3419 := by
    have hnat : (272172521 : ℕ)^4443*100000000000000^3419 ≤ 45369906274063^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272172521 500000000 45369906274063 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208433391/400000000 : ℝ)^4443 ≤ (1714668796727/4000000000000 : ℝ)^3419 := by
    have hnat : (208433391 : ℕ)^4443*4000000000000^3419 ≤ 1714668796727^3419*400000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208433391 400000000 1714668796727 4000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1926419961/10000000000 : ℝ), (272172521/500000000 : ℝ), (208433391/400000000 : ℝ)] ![(11763373800389/100000000000000 : ℝ), (45369906274063/100000000000000 : ℝ), (1714668796727/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1926419961/10000000000 : ℝ)|^4443 ≤ (11763373800389/100000000000000 : ℝ)^3419
        have hw : |(-1926419961/10000000000 : ℝ)|=(1926419961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272172521/500000000 : ℝ)|^4443 ≤ (45369906274063/100000000000000 : ℝ)^3419
        have hw : |(272172521/500000000 : ℝ)|=(272172521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208433391/400000000 : ℝ)|^4443 ≤ (1714668796727/4000000000000 : ℝ)^3419
        have hw : |(208433391/400000000 : ℝ)|=(208433391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677493853/5000000000 : ℝ)*x 0 + (-2045779287/10000000000 : ℝ)*x 1 + (651354337/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677493853/5000000000 : ℝ)^4443 ≤ (11103525577247/25000000000000 : ℝ)^3419 := by
    have hnat : (2677493853 : ℕ)^4443*25000000000000^3419 ≤ 11103525577247^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677493853 5000000000 11103525577247 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045779287/10000000000 : ℝ)^4443 ≤ (12719178613439/100000000000000 : ℝ)^3419 := by
    have hnat : (2045779287 : ℕ)^4443*100000000000000^3419 ≤ 12719178613439^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045779287 10000000000 12719178613439 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651354337/1250000000 : ℝ)^4443 ≤ (42866719073641/100000000000000 : ℝ)^3419 := by
    have hnat : (651354337 : ℕ)^4443*100000000000000^3419 ≤ 42866719073641^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651354337 1250000000 42866719073641 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677493853/5000000000 : ℝ), (-2045779287/10000000000 : ℝ), (651354337/1250000000 : ℝ)] ![(11103525577247/25000000000000 : ℝ), (12719178613439/100000000000000 : ℝ), (42866719073641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677493853/5000000000 : ℝ)|^4443 ≤ (11103525577247/25000000000000 : ℝ)^3419
        have hw : |(2677493853/5000000000 : ℝ)|=(2677493853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045779287/10000000000 : ℝ)|^4443 ≤ (12719178613439/100000000000000 : ℝ)^3419
        have hw : |(-2045779287/10000000000 : ℝ)|=(2045779287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651354337/1250000000 : ℝ)|^4443 ≤ (42866719073641/100000000000000 : ℝ)^3419
        have hw : |(651354337/1250000000 : ℝ)|=(651354337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338746923/2500000000 : ℝ)*x 0 + (5210834743/10000000000 : ℝ)*x 1 + (-2045779241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338746923/2500000000 : ℝ)^4443 ≤ (2775881384881/6250000000000 : ℝ)^3419 := by
    have hnat : (1338746923 : ℕ)^4443*6250000000000^3419 ≤ 2775881384881^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338746923 2500000000 2775881384881 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5210834743/10000000000 : ℝ)^4443 ≤ (8573343915217/20000000000000 : ℝ)^3419 := by
    have hnat : (5210834743 : ℕ)^4443*20000000000000^3419 ≤ 8573343915217^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210834743 10000000000 8573343915217 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045779241/10000000000 : ℝ)^4443 ≤ (3179794560447/25000000000000 : ℝ)^3419 := by
    have hnat : (2045779241 : ℕ)^4443*25000000000000^3419 ≤ 3179794560447^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045779241 10000000000 3179794560447 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338746923/2500000000 : ℝ), (5210834743/10000000000 : ℝ), (-2045779241/10000000000 : ℝ)] ![(2775881384881/6250000000000 : ℝ), (8573343915217/20000000000000 : ℝ), (3179794560447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338746923/2500000000 : ℝ)|^4443 ≤ (2775881384881/6250000000000 : ℝ)^3419
        have hw : |(1338746923/2500000000 : ℝ)|=(1338746923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5210834743/10000000000 : ℝ)|^4443 ≤ (8573343915217/20000000000000 : ℝ)^3419
        have hw : |(5210834743/10000000000 : ℝ)|=(5210834743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045779241/10000000000 : ℝ)|^4443 ≤ (3179794560447/25000000000000 : ℝ)^3419
        have hw : |(-2045779241/10000000000 : ℝ)|=(2045779241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287796809/10000000000 : ℝ)*x 0 + (252376261/625000000 : ℝ)*x 1 + (4551033037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287796809/10000000000 : ℝ)^4443 ≤ (8318161066571/25000000000000 : ℝ)^3419 := by
    have hnat : (4287796809 : ℕ)^4443*25000000000000^3419 ≤ 8318161066571^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287796809 10000000000 8318161066571 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252376261/625000000 : ℝ)^4443 ≤ (15388094891287/50000000000000 : ℝ)^3419 := by
    have hnat : (252376261 : ℕ)^4443*50000000000000^3419 ≤ 15388094891287^3419*625000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252376261 625000000 15388094891287 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4551033037/10000000000 : ℝ)^4443 ≤ (35951165939909/100000000000000 : ℝ)^3419 := by
    have hnat : (4551033037 : ℕ)^4443*100000000000000^3419 ≤ 35951165939909^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551033037 10000000000 35951165939909 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287796809/10000000000 : ℝ), (252376261/625000000 : ℝ), (4551033037/10000000000 : ℝ)] ![(8318161066571/25000000000000 : ℝ), (15388094891287/50000000000000 : ℝ), (35951165939909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287796809/10000000000 : ℝ)|^4443 ≤ (8318161066571/25000000000000 : ℝ)^3419
        have hw : |(4287796809/10000000000 : ℝ)|=(4287796809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252376261/625000000 : ℝ)|^4443 ≤ (15388094891287/50000000000000 : ℝ)^3419
        have hw : |(252376261/625000000 : ℝ)|=(252376261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4551033037/10000000000 : ℝ)|^4443 ≤ (35951165939909/100000000000000 : ℝ)^3419
        have hw : |(4551033037/10000000000 : ℝ)|=(4551033037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-963227333/5000000000 : ℝ)*x 0 + (1303018613/2500000000 : ℝ)*x 1 + (5442201339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963227333/5000000000 : ℝ)^4443 ≤ (2352729838483/20000000000000 : ℝ)^3419 := by
    have hnat : (963227333 : ℕ)^4443*20000000000000^3419 ≤ 2352729838483^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963227333 5000000000 2352729838483 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303018613/2500000000 : ℝ)^4443 ≤ (8575994583513/20000000000000 : ℝ)^3419 := by
    have hnat : (1303018613 : ℕ)^4443*20000000000000^3419 ≤ 8575994583513^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303018613 2500000000 8575994583513 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442201339/10000000000 : ℝ)^4443 ≤ (45356377872043/100000000000000 : ℝ)^3419 := by
    have hnat : (5442201339 : ℕ)^4443*100000000000000^3419 ≤ 45356377872043^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442201339 10000000000 45356377872043 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-963227333/5000000000 : ℝ), (1303018613/2500000000 : ℝ), (5442201339/10000000000 : ℝ)] ![(2352729838483/20000000000000 : ℝ), (8575994583513/20000000000000 : ℝ), (45356377872043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-963227333/5000000000 : ℝ)|^4443 ≤ (2352729838483/20000000000000 : ℝ)^3419
        have hw : |(-963227333/5000000000 : ℝ)|=(963227333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303018613/2500000000 : ℝ)|^4443 ≤ (8575994583513/20000000000000 : ℝ)^3419
        have hw : |(1303018613/2500000000 : ℝ)|=(1303018613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442201339/10000000000 : ℝ)|^4443 ≤ (45356377872043/100000000000000 : ℝ)^3419
        have hw : |(5442201339/10000000000 : ℝ)|=(5442201339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529430751/1000000000 : ℝ)*x 0 + (-1814412719/10000000000 : ℝ)*x 1 + (1088440277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529430751/1000000000 : ℝ)^4443 ≤ (43761201736207/100000000000000 : ℝ)^3419 := by
    have hnat : (529430751 : ℕ)^4443*100000000000000^3419 ≤ 43761201736207^3419*1000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529430751 1000000000 43761201736207 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814412719/10000000000 : ℝ)^4443 ≤ (10882419879393/100000000000000 : ℝ)^3419 := by
    have hnat : (1814412719 : ℕ)^4443*100000000000000^3419 ≤ 10882419879393^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814412719 10000000000 10882419879393 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088440277/2000000000 : ℝ)^4443 ≤ (45356378370237/100000000000000 : ℝ)^3419 := by
    have hnat : (1088440277 : ℕ)^4443*100000000000000^3419 ≤ 45356378370237^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088440277 2000000000 45356378370237 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529430751/1000000000 : ℝ), (-1814412719/10000000000 : ℝ), (1088440277/2000000000 : ℝ)] ![(43761201736207/100000000000000 : ℝ), (10882419879393/100000000000000 : ℝ), (45356378370237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529430751/1000000000 : ℝ)|^4443 ≤ (43761201736207/100000000000000 : ℝ)^3419
        have hw : |(529430751/1000000000 : ℝ)|=(529430751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1814412719/10000000000 : ℝ)|^4443 ≤ (10882419879393/100000000000000 : ℝ)^3419
        have hw : |(-1814412719/10000000000 : ℝ)|=(1814412719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088440277/2000000000 : ℝ)|^4443 ≤ (45356378370237/100000000000000 : ℝ)^3419
        have hw : |(1088440277/2000000000 : ℝ)|=(1088440277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294307569/10000000000 : ℝ)*x 0 + (5442201391/10000000000 : ℝ)*x 1 + (-1814412629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294307569/10000000000 : ℝ)^4443 ≤ (5470150296243/12500000000000 : ℝ)^3419 := by
    have hnat : (5294307569 : ℕ)^4443*12500000000000^3419 ≤ 5470150296243^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294307569 10000000000 5470150296243 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442201391/10000000000 : ℝ)^4443 ≤ (45356378435219/100000000000000 : ℝ)^3419 := by
    have hnat : (5442201391 : ℕ)^4443*100000000000000^3419 ≤ 45356378435219^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442201391 10000000000 45356378435219 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1814412629/10000000000 : ℝ)^4443 ≤ (10882419177923/100000000000000 : ℝ)^3419 := by
    have hnat : (1814412629 : ℕ)^4443*100000000000000^3419 ≤ 10882419177923^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814412629 10000000000 10882419177923 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294307569/10000000000 : ℝ), (5442201391/10000000000 : ℝ), (-1814412629/10000000000 : ℝ)] ![(5470150296243/12500000000000 : ℝ), (45356378435219/100000000000000 : ℝ), (10882419177923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294307569/10000000000 : ℝ)|^4443 ≤ (5470150296243/12500000000000 : ℝ)^3419
        have hw : |(5294307569/10000000000 : ℝ)|=(5294307569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442201391/10000000000 : ℝ)|^4443 ≤ (45356378435219/100000000000000 : ℝ)^3419
        have hw : |(5442201391/10000000000 : ℝ)|=(5442201391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1814412629/10000000000 : ℝ)|^4443 ≤ (10882419177923/100000000000000 : ℝ)^3419
        have hw : |(-1814412629/10000000000 : ℝ)|=(1814412629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s3_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143936809/5000000000 : ℝ)*x 0 + (1137074857/2500000000 : ℝ)*x 1 + (202038737/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143936809/5000000000 : ℝ)^4443 ≤ (33273418805851/100000000000000 : ℝ)^3419 := by
    have hnat : (2143936809 : ℕ)^4443*100000000000000^3419 ≤ 33273418805851^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143936809 5000000000 33273418805851 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137074857/2500000000 : ℝ)^4443 ≤ (17961553297487/50000000000000 : ℝ)^3419 := by
    have hnat : (1137074857 : ℕ)^4443*50000000000000^3419 ≤ 17961553297487^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137074857 2500000000 17961553297487 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202038737/500000000 : ℝ)^4443 ≤ (15401737292149/50000000000000 : ℝ)^3419 := by
    have hnat : (202038737 : ℕ)^4443*50000000000000^3419 ≤ 15401737292149^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202038737 500000000 15401737292149 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143936809/5000000000 : ℝ), (1137074857/2500000000 : ℝ), (202038737/500000000 : ℝ)] ![(33273418805851/100000000000000 : ℝ), (17961553297487/50000000000000 : ℝ), (15401737292149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143936809/5000000000 : ℝ)|^4443 ≤ (33273418805851/100000000000000 : ℝ)^3419
        have hw : |(2143936809/5000000000 : ℝ)|=(2143936809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1137074857/2500000000 : ℝ)|^4443 ≤ (17961553297487/50000000000000 : ℝ)^3419
        have hw : |(1137074857/2500000000 : ℝ)|=(1137074857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202038737/500000000 : ℝ)|^4443 ≤ (15401737292149/50000000000000 : ℝ)^3419
        have hw : |(202038737/500000000 : ℝ)|=(202038737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5329/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (779/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4041/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5061/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4041/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5061/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4041/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5061/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4041/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5061/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4041/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5061/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4041/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5061/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5061/50000 : ℝ) ^ (4441/1024 : ℝ) ≤ (4852053390097361/100000000000000000000 : ℝ) := by
    have hpowers : (5061/50000 : ℝ)^4441 ≤ (4852053390097361/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5061 : ℕ)^4441*100000000000000000000^1024 ≤ 4852053390097361^1024*50000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5061 50000 4852053390097361 100000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5061/50000 : ℝ)) (X := (4852053390097361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4041/25000 : ℝ) ^ (4441/1024 : ℝ) ≤ (18472018141331867/50000000000000000000 : ℝ) := by
    have hpowers : (4041/25000 : ℝ)^4441 ≤ (18472018141331867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4041 : ℕ)^4441*50000000000000000000^1024 ≤ 18472018141331867^1024*25000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4041 25000 18472018141331867 50000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4041/25000 : ℝ)) (X := (18472018141331867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004852053390097361/50000000000000000000 : ℝ) ≤ (5000111873839097/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50004852053390097361/50000000000000000000 : ℝ)^1024 ≤ (5000111873839097/5000000000000000 : ℝ)^4441 := by
      have hnat : (50004852053390097361 : ℕ)^1024*5000000000000000^4441 ≤ 5000111873839097^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004852053390097361 50000000000000000000 5000111873839097 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000111873839097/5000000000000000 : ℝ)) (X := (50004852053390097361/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008359217934552219/20000000000000000000 : ℝ) ≤ (10000963573872251/10000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (20008359217934552219/20000000000000000000 : ℝ)^1024 ≤ (10000963573872251/10000000000000000 : ℝ)^4441 := by
      have hnat : (20008359217934552219 : ℕ)^1024*10000000000000000^4441 ≤ 10000963573872251^4441*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008359217934552219 20000000000000000000 10000963573872251 10000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000963573872251/10000000000000000 : ℝ)) (X := (20008359217934552219/20000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018472018141331867/25000000000000000000 : ℝ) ≤ (2500425850016577/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (25018472018141331867/25000000000000000000 : ℝ)^1024 ≤ (2500425850016577/2500000000000000 : ℝ)^4441 := by
      have hnat : (25018472018141331867 : ℕ)^1024*2500000000000000^4441 ≤ 2500425850016577^4441*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018472018141331867 25000000000000000000 2500425850016577 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500425850016577/2500000000000000 : ℝ)) (X := (25018472018141331867/25000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4852053390097361/100000000000000000000 : ℝ) ≤ ((125846614254164913/125875000000000000 : ℝ)+2*(739826194057/604200000000000 : ℝ)*(5061/50000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (125846614254164913/125875000000000000 : ℝ)+2*(739826194057/604200000000000 : ℝ)*(5061/50000 : ℝ)=(5000111873839097/5000000000000000 : ℝ) by norm_num, show 1+2*(4852053390097361/100000000000000000000 : ℝ)=(50004852053390097361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18472018141331867/50000000000000000000 : ℝ)+(4852053390097361/100000000000000000000 : ℝ) ≤ ((125846614254164913/125875000000000000 : ℝ)+(739826194057/604200000000000 : ℝ)*((4041/25000 : ℝ)+(5061/50000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (125846614254164913/125875000000000000 : ℝ)+(739826194057/604200000000000 : ℝ)*((4041/25000 : ℝ)+(5061/50000 : ℝ))=(10000963573872251/10000000000000000 : ℝ) by norm_num, show 1+(18472018141331867/50000000000000000000 : ℝ)+(4852053390097361/100000000000000000000 : ℝ)=(20008359217934552219/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18472018141331867/50000000000000000000 : ℝ) ≤ ((125846614254164913/125875000000000000 : ℝ)+2*(739826194057/604200000000000 : ℝ)*(4041/25000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (125846614254164913/125875000000000000 : ℝ)+2*(739826194057/604200000000000 : ℝ)*(4041/25000 : ℝ)=(2500425850016577/2500000000000000 : ℝ) by norm_num, show 1+2*(18472018141331867/50000000000000000000 : ℝ)=(25018472018141331867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125846614254164913/125875000000000000 : ℝ)*(X 1 0+X 2 0)+(739826194057/604200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5061/50000 : ℝ)) (hi := (4041/25000 : ℝ)) (c := (125846614254164913/125875000000000000 : ℝ)) (alpha := (739826194057/604200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125846614254164913/125875000000000000 : ℝ)*(X 0 1+X 2 1)+(739826194057/604200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5061/50000 : ℝ)) (hi := (4041/25000 : ℝ)) (c := (125846614254164913/125875000000000000 : ℝ)) (alpha := (739826194057/604200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125846614254164913/125875000000000000 : ℝ)*(X 0 2+X 1 2)+(739826194057/604200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5061/50000 : ℝ)) (hi := (4041/25000 : ℝ)) (c := (125846614254164913/125875000000000000 : ℝ)) (alpha := (739826194057/604200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1926419961/10000000000 : ℝ)*X 0 0+(272172521/500000000 : ℝ)*X 0 1+(208433391/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677493853/5000000000 : ℝ)*X 1 0+(-2045779287/10000000000 : ℝ)*X 1 1+(651354337/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338746923/2500000000 : ℝ)*X 2 0+(5210834743/10000000000 : ℝ)*X 2 1+(-2045779241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4287796809/10000000000 : ℝ)*X 0 0+(252376261/625000000 : ℝ)*X 0 1+(4551033037/10000000000 : ℝ)*X 0 2+(4287796809/10000000000 : ℝ)*X 1 0+(252376261/625000000 : ℝ)*X 1 1+(4551033037/10000000000 : ℝ)*X 1 2+(4287796809/10000000000 : ℝ)*X 2 0+(252376261/625000000 : ℝ)*X 2 1+(4551033037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-963227333/5000000000 : ℝ)*X 0 0+(1303018613/2500000000 : ℝ)*X 0 1+(5442201339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529430751/1000000000 : ℝ)*X 1 0+(-1814412719/10000000000 : ℝ)*X 1 1+(1088440277/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294307569/10000000000 : ℝ)*X 2 0+(5442201391/10000000000 : ℝ)*X 2 1+(-1814412629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143936809/5000000000 : ℝ)*X 0 0+(1137074857/2500000000 : ℝ)*X 0 1+(202038737/500000000 : ℝ)*X 0 2+(2143936809/5000000000 : ℝ)*X 1 0+(1137074857/2500000000 : ℝ)*X 1 1+(202038737/500000000 : ℝ)*X 1 2+(2143936809/5000000000 : ℝ)*X 2 0+(1137074857/2500000000 : ℝ)*X 2 1+(202038737/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17595107565486567339513789/3146875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (555320941/50000000000000 : ℝ)*(base19) + (52775697/5000000000000 : ℝ)*(base23) + (2350239/10000000000000 : ℝ)*(lower2) + (59605493/50000000000000 : ℝ)*(upper3) + (124792921/100000000000000 : ℝ)*(upper5) + (390515745496077/12500000000000 : ℝ)*(major0) + (390515745496077/12500000000000 : ℝ)*(major1) + (390515745496077/12500000000000 : ℝ)*(major2) + (2149476337332697/50000000000000 : ℝ)*(sp0) + (2149483966684357/50000000000000 : ℝ)*(sp1) + (268685499281041/6250000000000 : ℝ)*(sp2) + (1949275718167961/100000000000000 : ℝ)*(sp3) + (16369345203/100000000000000 : ℝ)*(sp4) + (6979382153/100000000000000 : ℝ)*(sp7) + (974641348775057/50000000000000 : ℝ)*(f.failure) + (1074742261002649/25000000000000 : ℝ)*(f.sum) + (5398902159867/5035000000000000000000000000 : ℝ)*base65 + (610271175987443/49169921875000000000000000000 : ℝ)*base67 + (372518029131193/49169921875000000000000000000 : ℝ)*base69 + (13485543039393227/3146875000000000000000000000000 : ℝ)*base71 + (5936745790641/2517500000000000000000000000 : ℝ)*base73 + (48361610859899477/3146875000000000000000000000000 : ℝ)*base75 + (14026403154780727/3146875000000000000000000000000 : ℝ)*base77 + (10889110477358463/786718750000000000000000000000 : ℝ)*base79 + (5280854017017/5035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (29754049/5000000000000000000000 : ℝ)*base90 + (29754049/5000000000000000000000 : ℝ)*base92 + (29754049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6014858914266853239047223/629375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136850819/10000000000000 : ℝ)*(base19) + (839138867/50000000000000 : ℝ)*(base23) + (102292101/50000000000000 : ℝ)*(upper3) + (102079263/100000000000000 : ℝ)*(lower4) + (29484639/20000000000000 : ℝ)*(upper5) + (157894354136667/5000000000000 : ℝ)*(major0) + (157894354136667/5000000000000 : ℝ)*(major1) + (157894354136667/5000000000000 : ℝ)*(major2) + (3796080009/20000000000000 : ℝ)*(sp1) + (24960017897/100000000000000 : ℝ)*(sp2) + (1086356517234721/25000000000000 : ℝ)*(sp4) + (86908114400613/2000000000000 : ℝ)*(sp5) + (1086349857660813/25000000000000 : ℝ)*(sp6) + (1970347777965249/100000000000000 : ℝ)*(sp7) + (1970347777965249/100000000000000 : ℝ)*(f.failure) + (1086356517234721/25000000000000 : ℝ)*(f.sum) + (104763744481/50350000000000000000000000 : ℝ)*base66 + (24332679526503/19667968750000000000000000000 : ℝ)*base67 + (475046929403899/157343750000000000000000000000 : ℝ)*base69 + (256598228073899/157343750000000000000000000000 : ℝ)*base71 + (2528260712197/1007000000000000000000000000 : ℝ)*base73 + (89773958460327/314687500000000000000000000000 : ℝ)*base76 + (1622447915243423/314687500000000000000000000000 : ℝ)*base77 + (1028653990444971/629375000000000000000000000000 : ℝ)*base79 + (2000854981679/1007000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (107639793/10000000000000000000000 : ℝ)*base90 + (107639793/10000000000000000000000 : ℝ)*base92 + (107639793/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1473_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (779/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1473_s4_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-240887531/1250000000 : ℝ)*x 0 + (217562279/400000000 : ℝ)*x 1 + (651847511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240887531/1250000000 : ℝ)^4443 ≤ (11768772302511/100000000000000 : ℝ)^3419 := by
    have hnat : (240887531 : ℕ)^4443*100000000000000^3419 ≤ 11768772302511^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240887531 1250000000 11768772302511 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217562279/400000000 : ℝ)^4443 ≤ (22661163187703/50000000000000 : ℝ)^3419 := by
    have hnat : (217562279 : ℕ)^4443*50000000000000^3419 ≤ 22661163187703^3419*400000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217562279 400000000 22661163187703 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651847511/1250000000 : ℝ)^4443 ≤ (10727225326301/25000000000000 : ℝ)^3419 := by
    have hnat : (651847511 : ℕ)^4443*25000000000000^3419 ≤ 10727225326301^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651847511 1250000000 10727225326301 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240887531/1250000000 : ℝ), (217562279/400000000 : ℝ), (651847511/1250000000 : ℝ)] ![(11768772302511/100000000000000 : ℝ), (22661163187703/50000000000000 : ℝ), (10727225326301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240887531/1250000000 : ℝ)|^4443 ≤ (11768772302511/100000000000000 : ℝ)^3419
        have hw : |(-240887531/1250000000 : ℝ)|=(240887531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217562279/400000000 : ℝ)|^4443 ≤ (22661163187703/50000000000000 : ℝ)^3419
        have hw : |(217562279/400000000 : ℝ)|=(217562279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651847511/1250000000 : ℝ)|^4443 ≤ (10727225326301/25000000000000 : ℝ)^3419
        have hw : |(651847511/1250000000 : ℝ)|=(651847511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353849673/10000000000 : ℝ)*x 0 + (-408415139/2000000000 : ℝ)*x 1 + (5214779873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353849673/10000000000 : ℝ)^4443 ≤ (11100459234729/25000000000000 : ℝ)^3419 := by
    have hnat : (5353849673 : ℕ)^4443*25000000000000^3419 ≤ 11100459234729^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353849673 10000000000 11100459234729 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408415139/2000000000 : ℝ)^4443 ≤ (12689264038647/100000000000000 : ℝ)^3419 := by
    have hnat : (408415139 : ℕ)^4443*100000000000000^3419 ≤ 12689264038647^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408415139 2000000000 12689264038647 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214779873/10000000000 : ℝ)^4443 ≤ (42908899006267/100000000000000 : ℝ)^3419 := by
    have hnat : (5214779873 : ℕ)^4443*100000000000000^3419 ≤ 42908899006267^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214779873 10000000000 42908899006267 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353849673/10000000000 : ℝ), (-408415139/2000000000 : ℝ), (5214779873/10000000000 : ℝ)] ![(11100459234729/25000000000000 : ℝ), (12689264038647/100000000000000 : ℝ), (42908899006267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353849673/10000000000 : ℝ)|^4443 ≤ (11100459234729/25000000000000 : ℝ)^3419
        have hw : |(5353849673/10000000000 : ℝ)|=(5353849673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408415139/2000000000 : ℝ)|^4443 ≤ (12689264038647/100000000000000 : ℝ)^3419
        have hw : |(-408415139/2000000000 : ℝ)|=(408415139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214779873/10000000000 : ℝ)|^4443 ≤ (42908899006267/100000000000000 : ℝ)^3419
        have hw : |(5214779873/10000000000 : ℝ)|=(5214779873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353849561/10000000000 : ℝ)*x 0 + (5214780063/10000000000 : ℝ)*x 1 + (-2042075593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353849561/10000000000 : ℝ)^4443 ≤ (44401835731853/100000000000000 : ℝ)^3419 := by
    have hnat : (5353849561 : ℕ)^4443*100000000000000^3419 ≤ 44401835731853^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353849561 10000000000 44401835731853 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214780063/10000000000 : ℝ)^4443 ≤ (21454450518943/50000000000000 : ℝ)^3419 := by
    have hnat : (5214780063 : ℕ)^4443*50000000000000^3419 ≤ 21454450518943^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214780063 10000000000 21454450518943 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2042075593/10000000000 : ℝ)^4443 ≤ (6344631607499/50000000000000 : ℝ)^3419 := by
    have hnat : (2042075593 : ℕ)^4443*50000000000000^3419 ≤ 6344631607499^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042075593 10000000000 6344631607499 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353849561/10000000000 : ℝ), (5214780063/10000000000 : ℝ), (-2042075593/10000000000 : ℝ)] ![(44401835731853/100000000000000 : ℝ), (21454450518943/50000000000000 : ℝ), (6344631607499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353849561/10000000000 : ℝ)|^4443 ≤ (44401835731853/100000000000000 : ℝ)^3419
        have hw : |(5353849561/10000000000 : ℝ)|=(5353849561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214780063/10000000000 : ℝ)|^4443 ≤ (21454450518943/50000000000000 : ℝ)^3419
        have hw : |(5214780063/10000000000 : ℝ)|=(5214780063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2042075593/10000000000 : ℝ)|^4443 ≤ (6344631607499/50000000000000 : ℝ)^3419
        have hw : |(-2042075593/10000000000 : ℝ)|=(2042075593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33501719/78125000 : ℝ)*x 0 + (4047165157/10000000000 : ℝ)*x 1 + (4541788287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33501719/78125000 : ℝ)^4443 ≤ (6655382417097/20000000000000 : ℝ)^3419 := by
    have hnat : (33501719 : ℕ)^4443*20000000000000^3419 ≤ 6655382417097^3419*78125000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33501719 78125000 6655382417097 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4047165157/10000000000 : ℝ)^4443 ≤ (30866795076329/100000000000000 : ℝ)^3419 := by
    have hnat : (4047165157 : ℕ)^4443*100000000000000^3419 ≤ 30866795076329^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047165157 10000000000 30866795076329 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541788287/10000000000 : ℝ)^4443 ≤ (35856292820359/100000000000000 : ℝ)^3419 := by
    have hnat : (4541788287 : ℕ)^4443*100000000000000^3419 ≤ 35856292820359^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541788287 10000000000 35856292820359 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33501719/78125000 : ℝ), (4047165157/10000000000 : ℝ), (4541788287/10000000000 : ℝ)] ![(6655382417097/20000000000000 : ℝ), (30866795076329/100000000000000 : ℝ), (35856292820359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33501719/78125000 : ℝ)|^4443 ≤ (6655382417097/20000000000000 : ℝ)^3419
        have hw : |(33501719/78125000 : ℝ)|=(33501719/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4047165157/10000000000 : ℝ)|^4443 ≤ (30866795076329/100000000000000 : ℝ)^3419
        have hw : |(4047165157/10000000000 : ℝ)|=(4047165157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541788287/10000000000 : ℝ)|^4443 ≤ (35856292820359/100000000000000 : ℝ)^3419
        have hw : |(4541788287/10000000000 : ℝ)|=(4541788287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-481782983/2500000000 : ℝ)*x 0 + (5215932103/10000000000 : ℝ)*x 1 + (2718948051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481782983/2500000000 : ℝ)^4443 ≤ (11769023748747/100000000000000 : ℝ)^3419 := by
    have hnat : (481782983 : ℕ)^4443*100000000000000^3419 ≤ 11769023748747^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481782983 2500000000 11769023748747 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215932103/10000000000 : ℝ)^4443 ≤ (42921219898263/100000000000000 : ℝ)^3419 := by
    have hnat : (5215932103 : ℕ)^4443*100000000000000^3419 ≤ 42921219898263^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215932103 10000000000 42921219898263 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718948051/5000000000 : ℝ)^4443 ≤ (22654878168179/50000000000000 : ℝ)^3419 := by
    have hnat : (2718948051 : ℕ)^4443*50000000000000^3419 ≤ 22654878168179^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718948051 5000000000 22654878168179 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481782983/2500000000 : ℝ), (5215932103/10000000000 : ℝ), (2718948051/5000000000 : ℝ)] ![(11769023748747/100000000000000 : ℝ), (42921219898263/100000000000000 : ℝ), (22654878168179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481782983/2500000000 : ℝ)|^4443 ≤ (11769023748747/100000000000000 : ℝ)^3419
        have hw : |(-481782983/2500000000 : ℝ)|=(481782983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215932103/10000000000 : ℝ)|^4443 ≤ (42921219898263/100000000000000 : ℝ)^3419
        have hw : |(5215932103/10000000000 : ℝ)|=(5215932103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718948051/5000000000 : ℝ)|^4443 ≤ (22654878168179/50000000000000 : ℝ)^3419
        have hw : |(2718948051/5000000000 : ℝ)|=(2718948051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295347959/10000000000 : ℝ)*x 0 + (-1818959641/10000000000 : ℝ)*x 1 + (5437895493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295347959/10000000000 : ℝ)^4443 ≤ (4377237785133/10000000000000 : ℝ)^3419 := by
    have hnat : (5295347959 : ℕ)^4443*10000000000000^3419 ≤ 4377237785133^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295347959 10000000000 4377237785133 10000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1818959641/10000000000 : ℝ)^4443 ≤ (5458936193891/50000000000000 : ℝ)^3419 := by
    have hnat : (1818959641 : ℕ)^4443*50000000000000^3419 ≤ 5458936193891^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818959641 10000000000 5458936193891 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437895493/10000000000 : ℝ)^4443 ≤ (22654874871131/50000000000000 : ℝ)^3419 := by
    have hnat : (5437895493 : ℕ)^4443*50000000000000^3419 ≤ 22654874871131^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437895493 10000000000 22654874871131 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295347959/10000000000 : ℝ), (-1818959641/10000000000 : ℝ), (5437895493/10000000000 : ℝ)] ![(4377237785133/10000000000000 : ℝ), (5458936193891/50000000000000 : ℝ), (22654874871131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295347959/10000000000 : ℝ)|^4443 ≤ (4377237785133/10000000000000 : ℝ)^3419
        have hw : |(5295347959/10000000000 : ℝ)|=(5295347959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1818959641/10000000000 : ℝ)|^4443 ≤ (5458936193891/50000000000000 : ℝ)^3419
        have hw : |(-1818959641/10000000000 : ℝ)|=(1818959641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437895493/10000000000 : ℝ)|^4443 ≤ (22654874871131/50000000000000 : ℝ)^3419
        have hw : |(5437895493/10000000000 : ℝ)|=(5437895493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13238369/25000000 : ℝ)*x 0 + (5437895721/10000000000 : ℝ)*x 1 + (-90947991/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13238369/25000000 : ℝ)^4443 ≤ (10943093498743/25000000000000 : ℝ)^3419 := by
    have hnat : (13238369 : ℕ)^4443*25000000000000^3419 ≤ 10943093498743^3419*25000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13238369 25000000 10943093498743 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437895721/10000000000 : ℝ)^4443 ≤ (45309752210987/100000000000000 : ℝ)^3419 := by
    have hnat : (5437895721 : ℕ)^4443*100000000000000^3419 ≤ 45309752210987^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437895721 10000000000 45309752210987 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90947991/500000000 : ℝ)^4443 ≤ (5458936891987/50000000000000 : ℝ)^3419 := by
    have hnat : (90947991 : ℕ)^4443*50000000000000^3419 ≤ 5458936891987^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90947991 500000000 5458936891987 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13238369/25000000 : ℝ), (5437895721/10000000000 : ℝ), (-90947991/500000000 : ℝ)] ![(10943093498743/25000000000000 : ℝ), (45309752210987/100000000000000 : ℝ), (5458936891987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13238369/25000000 : ℝ)|^4443 ≤ (10943093498743/25000000000000 : ℝ)^3419
        have hw : |(13238369/25000000 : ℝ)|=(13238369/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437895721/10000000000 : ℝ)|^4443 ≤ (45309752210987/100000000000000 : ℝ)^3419
        have hw : |(5437895721/10000000000 : ℝ)|=(5437895721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90947991/500000000 : ℝ)|^4443 ≤ (5458936891987/50000000000000 : ℝ)^3419
        have hw : |(-90947991/500000000 : ℝ)|=(90947991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s4_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67004527/156250000 : ℝ)*x 0 + (4539245881/10000000000 : ℝ)*x 1 + (2024862759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67004527/156250000 : ℝ)^4443 ≤ (16638807459191/50000000000000 : ℝ)^3419 := by
    have hnat : (67004527 : ℕ)^4443*50000000000000^3419 ≤ 16638807459191^3419*156250000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67004527 156250000 16638807459191 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539245881/10000000000 : ℝ)^4443 ≤ (35830211822419/100000000000000 : ℝ)^3419 := by
    have hnat : (4539245881 : ℕ)^4443*100000000000000^3419 ≤ 35830211822419^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539245881 10000000000 35830211822419 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024862759/5000000000 : ℝ)^4443 ≤ (15446086619091/50000000000000 : ℝ)^3419 := by
    have hnat : (2024862759 : ℕ)^4443*50000000000000^3419 ≤ 15446086619091^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024862759 5000000000 15446086619091 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67004527/156250000 : ℝ), (4539245881/10000000000 : ℝ), (2024862759/5000000000 : ℝ)] ![(16638807459191/50000000000000 : ℝ), (35830211822419/100000000000000 : ℝ), (15446086619091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67004527/156250000 : ℝ)|^4443 ≤ (16638807459191/50000000000000 : ℝ)^3419
        have hw : |(67004527/156250000 : ℝ)|=(67004527/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539245881/10000000000 : ℝ)|^4443 ≤ (35830211822419/100000000000000 : ℝ)^3419
        have hw : |(4539245881/10000000000 : ℝ)|=(4539245881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2024862759/5000000000 : ℝ)|^4443 ≤ (15446086619091/50000000000000 : ℝ)^3419
        have hw : |(2024862759/5000000000 : ℝ)|=(2024862759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (779/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5371/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (779/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (779/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (779/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (779/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (779/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (779/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5329/50000 : ℝ) ^ (4441/1024 : ℝ) ≤ (151723603094099/2500000000000000000 : ℝ) := by
    have hpowers : (5329/50000 : ℝ)^4441 ≤ (151723603094099/2500000000000000000 : ℝ)^1024 := by
      have hnat : (5329 : ℕ)^4441*2500000000000000000^1024 ≤ 151723603094099^1024*50000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5329 50000 151723603094099 2500000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5329/50000 : ℝ)) (X := (151723603094099/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (779/5000 : ℝ) ^ (4441/1024 : ℝ) ≤ (31494479396084359/100000000000000000000 : ℝ) := by
    have hpowers : (779/5000 : ℝ)^4441 ≤ (31494479396084359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (779 : ℕ)^4441*100000000000000000000^1024 ≤ 31494479396084359^1024*5000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        779 5000 31494479396084359 100000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (779/5000 : ℝ)) (X := (31494479396084359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250151723603094099/1250000000000000000 : ℝ) ≤ (625017491298717/625000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (1250151723603094099/1250000000000000000 : ℝ)^1024 ≤ (625017491298717/625000000000000 : ℝ)^4441 := by
      have hnat : (1250151723603094099 : ℕ)^1024*625000000000000^4441 ≤ 625017491298717^4441*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250151723603094099 1250000000000000000 625017491298717 625000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017491298717/625000000000000 : ℝ)) (X := (1250151723603094099/1250000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037563423519848319/100000000000000000000 : ℝ) ≤ (2000173201478619/2000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (100037563423519848319/100000000000000000000 : ℝ)^1024 ≤ (2000173201478619/2000000000000000 : ℝ)^4441 := by
      have hnat : (100037563423519848319 : ℕ)^1024*2000000000000000^4441 ≤ 2000173201478619^4441*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037563423519848319 100000000000000000000 2000173201478619 2000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000173201478619/2000000000000000 : ℝ)) (X := (100037563423519848319/100000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031494479396084359/50000000000000000000 : ℝ) ≤ (5000726077003359/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50031494479396084359/50000000000000000000 : ℝ)^1024 ≤ (5000726077003359/5000000000000000 : ℝ)^4441 := by
      have hnat : (50031494479396084359 : ℕ)^1024*5000000000000000^4441 ≤ 5000726077003359^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031494479396084359 50000000000000000000 5000726077003359 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000726077003359/5000000000000000 : ℝ)) (X := (50031494479396084359/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(151723603094099/2500000000000000000 : ℝ) ≤ ((12302220793385143329/12305000000000000000 : ℝ)+2*(586146613623/492200000000000 : ℝ)*(5329/50000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (12302220793385143329/12305000000000000000 : ℝ)+2*(586146613623/492200000000000 : ℝ)*(5329/50000 : ℝ)=(625017491298717/625000000000000 : ℝ) by norm_num, show 1+2*(151723603094099/2500000000000000000 : ℝ)=(1250151723603094099/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31494479396084359/100000000000000000000 : ℝ)+(151723603094099/2500000000000000000 : ℝ) ≤ ((12302220793385143329/12305000000000000000 : ℝ)+(586146613623/492200000000000 : ℝ)*((779/5000 : ℝ)+(5329/50000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (12302220793385143329/12305000000000000000 : ℝ)+(586146613623/492200000000000 : ℝ)*((779/5000 : ℝ)+(5329/50000 : ℝ))=(2000173201478619/2000000000000000 : ℝ) by norm_num, show 1+(31494479396084359/100000000000000000000 : ℝ)+(151723603094099/2500000000000000000 : ℝ)=(100037563423519848319/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31494479396084359/100000000000000000000 : ℝ) ≤ ((12302220793385143329/12305000000000000000 : ℝ)+2*(586146613623/492200000000000 : ℝ)*(779/5000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (12302220793385143329/12305000000000000000 : ℝ)+2*(586146613623/492200000000000 : ℝ)*(779/5000 : ℝ)=(5000726077003359/5000000000000000 : ℝ) by norm_num, show 1+2*(31494479396084359/100000000000000000000 : ℝ)=(50031494479396084359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12302220793385143329/12305000000000000000 : ℝ)*(X 1 0+X 2 0)+(586146613623/492200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (779/5000 : ℝ)) (c := (12302220793385143329/12305000000000000000 : ℝ)) (alpha := (586146613623/492200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12302220793385143329/12305000000000000000 : ℝ)*(X 0 1+X 2 1)+(586146613623/492200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (779/5000 : ℝ)) (c := (12302220793385143329/12305000000000000000 : ℝ)) (alpha := (586146613623/492200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12302220793385143329/12305000000000000000 : ℝ)*(X 0 2+X 1 2)+(586146613623/492200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (779/5000 : ℝ)) (c := (12302220793385143329/12305000000000000000 : ℝ)) (alpha := (586146613623/492200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240887531/1250000000 : ℝ)*X 0 0+(217562279/400000000 : ℝ)*X 0 1+(651847511/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353849673/10000000000 : ℝ)*X 1 0+(-408415139/2000000000 : ℝ)*X 1 1+(5214779873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353849561/10000000000 : ℝ)*X 2 0+(5214780063/10000000000 : ℝ)*X 2 1+(-2042075593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((33501719/78125000 : ℝ)*X 0 0+(4047165157/10000000000 : ℝ)*X 0 1+(4541788287/10000000000 : ℝ)*X 0 2+(33501719/78125000 : ℝ)*X 1 0+(4047165157/10000000000 : ℝ)*X 1 1+(4541788287/10000000000 : ℝ)*X 1 2+(33501719/78125000 : ℝ)*X 2 0+(4047165157/10000000000 : ℝ)*X 2 1+(4541788287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-481782983/2500000000 : ℝ)*X 0 0+(5215932103/10000000000 : ℝ)*X 0 1+(2718948051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295347959/10000000000 : ℝ)*X 1 0+(-1818959641/10000000000 : ℝ)*X 1 1+(5437895493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((13238369/25000000 : ℝ)*X 2 0+(5437895721/10000000000 : ℝ)*X 2 1+(-90947991/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67004527/156250000 : ℝ)*X 0 0+(4539245881/10000000000 : ℝ)*X 0 1+(2024862759/5000000000 : ℝ)*X 0 2+(67004527/156250000 : ℝ)*X 1 0+(4539245881/10000000000 : ℝ)*X 1 1+(2024862759/5000000000 : ℝ)*X 1 2+(67004527/156250000 : ℝ)*X 2 0+(4539245881/10000000000 : ℝ)*X 2 1+(2024862759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1627500604302844745580978801/153812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379234877/20000000000000 : ℝ)*(base19) + (854125649/50000000000000 : ℝ)*(base23) + (25336163/50000000000000 : ℝ)*(lower2) + (46566303/25000000000000 : ℝ)*(upper3) + (97454907/50000000000000 : ℝ)*(upper5) + (810074746848177/25000000000000 : ℝ)*(major0) + (810074746848177/25000000000000 : ℝ)*(major1) + (810074746848177/25000000000000 : ℝ)*(major2) + (891760265521019/20000000000000 : ℝ)*(sp0) + (445882745412301/10000000000000 : ℝ)*(sp1) + (278676727627881/6250000000000 : ℝ)*(sp2) + (2021754721600553/100000000000000 : ℝ)*(sp3) + (28022692299/100000000000000 : ℝ)*(sp4) + (13550185179/100000000000000 : ℝ)*(sp7) + (505442067946433/25000000000000 : ℝ)*(f.failure) + (2229414675148697/50000000000000 : ℝ)*(f.sum) + (24055307491179/6152500000000000000000000000 : ℝ)*base66 + (1347078601871386233/307625000000000000000000000000000 : ℝ)*base67 + (1479101604864738767/307625000000000000000000000000000 : ℝ)*base70 + (76863354251886233/307625000000000000000000000000000 : ℝ)*base71 + (2034427070423/3076250000000000000000000000 : ℝ)*base73 + (1172495111863738767/307625000000000000000000000000000 : ℝ)*base76 + (1116301119491136233/307625000000000000000000000000000 : ℝ)*base77 + (2855203511673136233/307625000000000000000000000000000 : ℝ)*base79 + (110384026308483/12305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11823119/2500000000000000000000 : ℝ)*base89 + (11823119/2500000000000000000000 : ℝ)*base91 + (11823119/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (584575007665043952455361153/307625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1739405787/100000000000000 : ℝ)*(base19) + (4408989/312500000000 : ℝ)*(base23) + (42094861/100000000000000 : ℝ)*(upper2) + (75563973/100000000000000 : ℝ)*(upper3) + (336464487/100000000000000 : ℝ)*(upper5) + (1637012921245927/50000000000000 : ℝ)*(major0) + (1637012921245927/50000000000000 : ℝ)*(major1) + (1637012921245927/50000000000000 : ℝ)*(major2) + (248526991/1250000000000 : ℝ)*(sp1) + (10596145979/100000000000000 : ℝ)*(sp2) + (1126309912020497/25000000000000 : ℝ)*(sp4) + (4505218026516921/100000000000000 : ℝ)*(sp5) + (563153455132441/12500000000000 : ℝ)*(sp6) + (510702993389723/25000000000000 : ℝ)*(sp7) + (510702993389723/25000000000000 : ℝ)*(f.failure) + (1126309912020497/25000000000000 : ℝ)*(f.sum) + (14176850527279/12305000000000000000000000000 : ℝ)*base66 + (1241043233746495983/615250000000000000000000000000000 : ℝ)*base67 + (8532597262852495983/615250000000000000000000000000000 : ℝ)*base69 + (2600926347151745983/615250000000000000000000000000000 : ℝ)*base71 + (19238495045117/6152500000000000000000000000 : ℝ)*base74 + (2382128992468245983/615250000000000000000000000000000 : ℝ)*base75 + (5212805125966745983/615250000000000000000000000000000 : ℝ)*base77 + (5203846580231245983/615250000000000000000000000000000 : ℝ)*base79 + (7440368614519/3076250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (34170411/2500000000000000000000 : ℝ)*base90 + (34170411/2500000000000000000000 : ℝ)*base92 + (34170411/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1473_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (779/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1473_s5_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-481799541/2500000000 : ℝ)*x 0 + (5438438721/10000000000 : ℝ)*x 1 + (5215333497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481799541/2500000000 : ℝ)^4443 ≤ (2353909874821/20000000000000 : ℝ)^3419 := by
    have hnat : (481799541 : ℕ)^4443*20000000000000^3419 ≤ 2353909874821^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481799541 2500000000 2353909874821 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438438721/10000000000 : ℝ)^4443 ≤ (45315631764507/100000000000000 : ℝ)^3419 := by
    have hnat : (5438438721 : ℕ)^4443*100000000000000^3419 ≤ 45315631764507^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438438721 10000000000 45315631764507 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215333497/10000000000 : ℝ)^4443 ≤ (10728704713091/25000000000000 : ℝ)^3419 := by
    have hnat : (5215333497 : ℕ)^4443*25000000000000^3419 ≤ 10728704713091^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215333497 10000000000 10728704713091 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481799541/2500000000 : ℝ), (5438438721/10000000000 : ℝ), (5215333497/10000000000 : ℝ)] ![(2353909874821/20000000000000 : ℝ), (45315631764507/100000000000000 : ℝ), (10728704713091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481799541/2500000000 : ℝ)|^4443 ≤ (2353909874821/20000000000000 : ℝ)^3419
        have hw : |(-481799541/2500000000 : ℝ)|=(481799541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438438721/10000000000 : ℝ)|^4443 ≤ (45315631764507/100000000000000 : ℝ)^3419
        have hw : |(5438438721/10000000000 : ℝ)|=(5438438721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215333497/10000000000 : ℝ)|^4443 ≤ (10728704713091/25000000000000 : ℝ)^3419
        have hw : |(5215333497/10000000000 : ℝ)|=(5215333497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353689203/10000000000 : ℝ)*x 0 + (-510389403/2500000000 : ℝ)*x 1 + (2607666419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353689203/10000000000 : ℝ)^4443 ≤ (44400107505363/100000000000000 : ℝ)^3419 := by
    have hnat : (5353689203 : ℕ)^4443*100000000000000^3419 ≤ 44400107505363^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353689203 10000000000 44400107505363 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510389403/2500000000 : ℝ)^4443 ≤ (2537016136863/20000000000000 : ℝ)^3419 := by
    have hnat : (510389403 : ℕ)^4443*20000000000000^3419 ≤ 2537016136863^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510389403 2500000000 2537016136863 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607666419/5000000000 : ℝ)^4443 ≤ (42914811805631/100000000000000 : ℝ)^3419 := by
    have hnat : (2607666419 : ℕ)^4443*100000000000000^3419 ≤ 42914811805631^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607666419 5000000000 42914811805631 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353689203/10000000000 : ℝ), (-510389403/2500000000 : ℝ), (2607666419/5000000000 : ℝ)] ![(44400107505363/100000000000000 : ℝ), (2537016136863/20000000000000 : ℝ), (42914811805631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353689203/10000000000 : ℝ)|^4443 ≤ (44400107505363/100000000000000 : ℝ)^3419
        have hw : |(5353689203/10000000000 : ℝ)|=(5353689203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-510389403/2500000000 : ℝ)|^4443 ≤ (2537016136863/20000000000000 : ℝ)^3419
        have hw : |(-510389403/2500000000 : ℝ)|=(510389403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607666419/5000000000 : ℝ)|^4443 ≤ (42914811805631/100000000000000 : ℝ)^3419
        have hw : |(2607666419/5000000000 : ℝ)|=(2607666419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669211023/1250000000 : ℝ)*x 0 + (5215334841/10000000000 : ℝ)*x 1 + (-1020778159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669211023/1250000000 : ℝ)^4443 ≤ (22200048261671/50000000000000 : ℝ)^3419 := by
    have hnat : (669211023 : ℕ)^4443*50000000000000^3419 ≤ 22200048261671^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669211023 1250000000 22200048261671 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215334841/10000000000 : ℝ)^4443 ≤ (858296664477/2000000000000 : ℝ)^3419 := by
    have hnat : (5215334841 : ℕ)^4443*2000000000000^3419 ≤ 858296664477^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215334841 10000000000 858296664477 2000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020778159/5000000000 : ℝ)^4443 ≤ (6342535118039/50000000000000 : ℝ)^3419 := by
    have hnat : (1020778159 : ℕ)^4443*50000000000000^3419 ≤ 6342535118039^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020778159 5000000000 6342535118039 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669211023/1250000000 : ℝ), (5215334841/10000000000 : ℝ), (-1020778159/5000000000 : ℝ)] ![(22200048261671/50000000000000 : ℝ), (858296664477/2000000000000 : ℝ), (6342535118039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669211023/1250000000 : ℝ)|^4443 ≤ (22200048261671/50000000000000 : ℝ)^3419
        have hw : |(669211023/1250000000 : ℝ)|=(669211023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215334841/10000000000 : ℝ)|^4443 ≤ (858296664477/2000000000000 : ℝ)^3419
        have hw : |(5215334841/10000000000 : ℝ)|=(5215334841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020778159/5000000000 : ℝ)|^4443 ≤ (6342535118039/50000000000000 : ℝ)^3419
        have hw : |(-1020778159/5000000000 : ℝ)|=(1020778159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134008763/312500000 : ℝ)*x 0 + (4048448201/10000000000 : ℝ)*x 1 + (4540489327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134008763/312500000 : ℝ)^4443 ≤ (33277521013513/100000000000000 : ℝ)^3419 := by
    have hnat : (134008763 : ℕ)^4443*100000000000000^3419 ≤ 33277521013513^3419*312500000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134008763 312500000 33277521013513 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4048448201/10000000000 : ℝ)^4443 ≤ (30879511939243/100000000000000 : ℝ)^3419 := by
    have hnat : (4048448201 : ℕ)^4443*100000000000000^3419 ≤ 30879511939243^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048448201 10000000000 30879511939243 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540489327/10000000000 : ℝ)^4443 ≤ (8960741758181/25000000000000 : ℝ)^3419 := by
    have hnat : (4540489327 : ℕ)^4443*25000000000000^3419 ≤ 8960741758181^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540489327 10000000000 8960741758181 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134008763/312500000 : ℝ), (4048448201/10000000000 : ℝ), (4540489327/10000000000 : ℝ)] ![(33277521013513/100000000000000 : ℝ), (30879511939243/100000000000000 : ℝ), (8960741758181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134008763/312500000 : ℝ)|^4443 ≤ (33277521013513/100000000000000 : ℝ)^3419
        have hw : |(134008763/312500000 : ℝ)|=(134008763/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4048448201/10000000000 : ℝ)|^4443 ≤ (30879511939243/100000000000000 : ℝ)^3419
        have hw : |(4048448201/10000000000 : ℝ)|=(4048448201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540489327/10000000000 : ℝ)|^4443 ≤ (8960741758181/25000000000000 : ℝ)^3419
        have hw : |(4540489327/10000000000 : ℝ)|=(4540489327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-481806881/2500000000 : ℝ)*x 0 + (2608237253/5000000000 : ℝ)*x 1 + (2718645173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481806881/2500000000 : ℝ)^4443 ≤ (11769782380433/100000000000000 : ℝ)^3419 := by
    have hnat : (481806881 : ℕ)^4443*100000000000000^3419 ≤ 11769782380433^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481806881 2500000000 11769782380433 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608237253/5000000000 : ℝ)^4443 ≤ (5365877517653/12500000000000 : ℝ)^3419 := by
    have hnat : (2608237253 : ℕ)^4443*12500000000000^3419 ≤ 5365877517653^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608237253 5000000000 5365877517653 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718645173/5000000000 : ℝ)^4443 ≤ (2265159873703/5000000000000 : ℝ)^3419 := by
    have hnat : (2718645173 : ℕ)^4443*5000000000000^3419 ≤ 2265159873703^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718645173 5000000000 2265159873703 5000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481806881/2500000000 : ℝ), (2608237253/5000000000 : ℝ), (2718645173/5000000000 : ℝ)] ![(11769782380433/100000000000000 : ℝ), (5365877517653/12500000000000 : ℝ), (2265159873703/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481806881/2500000000 : ℝ)|^4443 ≤ (11769782380433/100000000000000 : ℝ)^3419
        have hw : |(-481806881/2500000000 : ℝ)|=(481806881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608237253/5000000000 : ℝ)|^4443 ≤ (5365877517653/12500000000000 : ℝ)^3419
        have hw : |(2608237253/5000000000 : ℝ)|=(2608237253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718645173/5000000000 : ℝ)|^4443 ≤ (2265159873703/5000000000000 : ℝ)^3419
        have hw : |(2718645173/5000000000 : ℝ)|=(2718645173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295492303/10000000000 : ℝ)*x 0 + (-1819600737/10000000000 : ℝ)*x 1 + (5437290433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295492303/10000000000 : ℝ)^4443 ≤ (43773928392699/100000000000000 : ℝ)^3419 := by
    have hnat : (5295492303 : ℕ)^4443*100000000000000^3419 ≤ 43773928392699^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295492303 10000000000 43773928392699 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1819600737/10000000000 : ℝ)^4443 ≤ (10922873172399/100000000000000 : ℝ)^3419 := by
    have hnat : (1819600737 : ℕ)^4443*100000000000000^3419 ≤ 10922873172399^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819600737 10000000000 10922873172399 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437290433/10000000000 : ℝ)^4443 ≤ (45303198416043/100000000000000 : ℝ)^3419 := by
    have hnat : (5437290433 : ℕ)^4443*100000000000000^3419 ≤ 45303198416043^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437290433 10000000000 45303198416043 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295492303/10000000000 : ℝ), (-1819600737/10000000000 : ℝ), (5437290433/10000000000 : ℝ)] ![(43773928392699/100000000000000 : ℝ), (10922873172399/100000000000000 : ℝ), (45303198416043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295492303/10000000000 : ℝ)|^4443 ≤ (43773928392699/100000000000000 : ℝ)^3419
        have hw : |(5295492303/10000000000 : ℝ)|=(5295492303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1819600737/10000000000 : ℝ)|^4443 ≤ (10922873172399/100000000000000 : ℝ)^3419
        have hw : |(-1819600737/10000000000 : ℝ)|=(1819600737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437290433/10000000000 : ℝ)|^4443 ≤ (45303198416043/100000000000000 : ℝ)^3419
        have hw : |(5437290433/10000000000 : ℝ)|=(5437290433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295492491/10000000000 : ℝ)*x 0 + (5437290539/10000000000 : ℝ)*x 1 + (-454900083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295492491/10000000000 : ℝ)^4443 ≤ (218869652061/500000000000 : ℝ)^3419 := by
    have hnat : (5295492491 : ℕ)^4443*500000000000^3419 ≤ 218869652061^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295492491 10000000000 218869652061 500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437290539/10000000000 : ℝ)^4443 ≤ (22651599781873/50000000000000 : ℝ)^3419 := by
    have hnat : (5437290539 : ℕ)^4443*50000000000000^3419 ≤ 22651599781873^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437290539 10000000000 22651599781873 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454900083/2500000000 : ℝ)^4443 ≤ (2730717503271/25000000000000 : ℝ)^3419 := by
    have hnat : (454900083 : ℕ)^4443*25000000000000^3419 ≤ 2730717503271^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454900083 2500000000 2730717503271 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295492491/10000000000 : ℝ), (5437290539/10000000000 : ℝ), (-454900083/2500000000 : ℝ)] ![(218869652061/500000000000 : ℝ), (22651599781873/50000000000000 : ℝ), (2730717503271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295492491/10000000000 : ℝ)|^4443 ≤ (218869652061/500000000000 : ℝ)^3419
        have hw : |(5295492491/10000000000 : ℝ)|=(5295492491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437290539/10000000000 : ℝ)|^4443 ≤ (22651599781873/50000000000000 : ℝ)^3419
        have hw : |(5437290539/10000000000 : ℝ)|=(5437290539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454900083/2500000000 : ℝ)|^4443 ≤ (2730717503271/25000000000000 : ℝ)^3419
        have hw : |(-454900083/2500000000 : ℝ)|=(454900083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s5_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288346421/10000000000 : ℝ)*x 0 + (4537973991/10000000000 : ℝ)*x 1 + (2025491921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288346421/10000000000 : ℝ)^4443 ≤ (2079886664257/6250000000000 : ℝ)^3419 := by
    have hnat : (4288346421 : ℕ)^4443*6250000000000^3419 ≤ 2079886664257^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288346421 10000000000 2079886664257 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537973991/10000000000 : ℝ)^4443 ≤ (17908582958763/50000000000000 : ℝ)^3419 := by
    have hnat : (4537973991 : ℕ)^4443*50000000000000^3419 ≤ 17908582958763^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537973991 10000000000 17908582958763 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025491921/5000000000 : ℝ)^4443 ≤ (30904647440151/100000000000000 : ℝ)^3419 := by
    have hnat : (2025491921 : ℕ)^4443*100000000000000^3419 ≤ 30904647440151^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025491921 5000000000 30904647440151 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288346421/10000000000 : ℝ), (4537973991/10000000000 : ℝ), (2025491921/5000000000 : ℝ)] ![(2079886664257/6250000000000 : ℝ), (17908582958763/50000000000000 : ℝ), (30904647440151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288346421/10000000000 : ℝ)|^4443 ≤ (2079886664257/6250000000000 : ℝ)^3419
        have hw : |(4288346421/10000000000 : ℝ)|=(4288346421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537973991/10000000000 : ℝ)|^4443 ≤ (17908582958763/50000000000000 : ℝ)^3419
        have hw : |(4537973991/10000000000 : ℝ)|=(4537973991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025491921/5000000000 : ℝ)|^4443 ≤ (30904647440151/100000000000000 : ℝ)^3419
        have hw : |(2025491921/5000000000 : ℝ)|=(2025491921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5377/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5371/50000 : ℝ) ^ (4441/1024 : ℝ) ≤ (6279131136386269/100000000000000000000 : ℝ) := by
    have hpowers : (5371/50000 : ℝ)^4441 ≤ (6279131136386269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5371 : ℕ)^4441*100000000000000000000^1024 ≤ 6279131136386269^1024*50000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5371 50000 6279131136386269 100000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5371/50000 : ℝ)) (X := (6279131136386269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4441/1024 : ℝ) ≤ (3836978910960021/12500000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4441 ≤ (3836978910960021/12500000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4441*12500000000000000000^1024 ≤ 3836978910960021^1024*3125^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 3836978910960021 12500000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (3836978910960021/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006279131136386269/50000000000000000000 : ℝ) ≤ (5000144776394111/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50006279131136386269/50000000000000000000 : ℝ)^1024 ≤ (5000144776394111/5000000000000000 : ℝ)^4441 := by
      have hnat : (50006279131136386269 : ℕ)^1024*5000000000000000^4441 ≤ 5000144776394111^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006279131136386269 50000000000000000000 5000144776394111 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000144776394111/5000000000000000 : ℝ)) (X := (50006279131136386269/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036974962424066437/100000000000000000000 : ℝ) ≤ (2500213110655841/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (100036974962424066437/100000000000000000000 : ℝ)^1024 ≤ (2500213110655841/2500000000000000 : ℝ)^4441 := by
      have hnat : (100036974962424066437 : ℕ)^1024*2500000000000000^4441 ≤ 2500213110655841^4441*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036974962424066437 100000000000000000000 2500213110655841 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500213110655841/2500000000000000 : ℝ)) (X := (100036974962424066437/100000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253836978910960021/6250000000000000000 : ℝ) ≤ (5000707666229253/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (6253836978910960021/6250000000000000000 : ℝ)^1024 ≤ (5000707666229253/5000000000000000 : ℝ)^4441 := by
      have hnat : (6253836978910960021 : ℕ)^1024*5000000000000000^4441 ≤ 5000707666229253^4441*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253836978910960021 6250000000000000000 5000707666229253 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000707666229253/5000000000000000 : ℝ)) (X := (6253836978910960021/6250000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6279131136386269/100000000000000000000 : ℝ) ≤ ((11862320273078677721/11865000000000000000 : ℝ)+2*(281444917571/237300000000000 : ℝ)*(5371/50000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (11862320273078677721/11865000000000000000 : ℝ)+2*(281444917571/237300000000000 : ℝ)*(5371/50000 : ℝ)=(5000144776394111/5000000000000000 : ℝ) by norm_num, show 1+2*(6279131136386269/100000000000000000000 : ℝ)=(50006279131136386269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3836978910960021/12500000000000000000 : ℝ)+(6279131136386269/100000000000000000000 : ℝ) ≤ ((11862320273078677721/11865000000000000000 : ℝ)+(281444917571/237300000000000 : ℝ)*((484/3125 : ℝ)+(5371/50000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (11862320273078677721/11865000000000000000 : ℝ)+(281444917571/237300000000000 : ℝ)*((484/3125 : ℝ)+(5371/50000 : ℝ))=(2500213110655841/2500000000000000 : ℝ) by norm_num, show 1+(3836978910960021/12500000000000000000 : ℝ)+(6279131136386269/100000000000000000000 : ℝ)=(100036974962424066437/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3836978910960021/12500000000000000000 : ℝ) ≤ ((11862320273078677721/11865000000000000000 : ℝ)+2*(281444917571/237300000000000 : ℝ)*(484/3125 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (11862320273078677721/11865000000000000000 : ℝ)+2*(281444917571/237300000000000 : ℝ)*(484/3125 : ℝ)=(5000707666229253/5000000000000000 : ℝ) by norm_num, show 1+2*(3836978910960021/12500000000000000000 : ℝ)=(6253836978910960021/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11862320273078677721/11865000000000000000 : ℝ)*(X 1 0+X 2 0)+(281444917571/237300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (11862320273078677721/11865000000000000000 : ℝ)) (alpha := (281444917571/237300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11862320273078677721/11865000000000000000 : ℝ)*(X 0 1+X 2 1)+(281444917571/237300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (11862320273078677721/11865000000000000000 : ℝ)) (alpha := (281444917571/237300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11862320273078677721/11865000000000000000 : ℝ)*(X 0 2+X 1 2)+(281444917571/237300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (11862320273078677721/11865000000000000000 : ℝ)) (alpha := (281444917571/237300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-481799541/2500000000 : ℝ)*X 0 0+(5438438721/10000000000 : ℝ)*X 0 1+(5215333497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353689203/10000000000 : ℝ)*X 1 0+(-510389403/2500000000 : ℝ)*X 1 1+(2607666419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669211023/1250000000 : ℝ)*X 2 0+(5215334841/10000000000 : ℝ)*X 2 1+(-1020778159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134008763/312500000 : ℝ)*X 0 0+(4048448201/10000000000 : ℝ)*X 0 1+(4540489327/10000000000 : ℝ)*X 0 2+(134008763/312500000 : ℝ)*X 1 0+(4048448201/10000000000 : ℝ)*X 1 1+(4540489327/10000000000 : ℝ)*X 1 2+(134008763/312500000 : ℝ)*X 2 0+(4048448201/10000000000 : ℝ)*X 2 1+(4540489327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-481806881/2500000000 : ℝ)*X 0 0+(2608237253/5000000000 : ℝ)*X 0 1+(2718645173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295492303/10000000000 : ℝ)*X 1 0+(-1819600737/10000000000 : ℝ)*X 1 1+(5437290433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295492491/10000000000 : ℝ)*X 2 0+(5437290539/10000000000 : ℝ)*X 2 1+(-454900083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4288346421/10000000000 : ℝ)*X 0 0+(4537973991/10000000000 : ℝ)*X 0 1+(2025491921/5000000000 : ℝ)*X 0 2+(4288346421/10000000000 : ℝ)*X 1 0+(4537973991/10000000000 : ℝ)*X 1 1+(2025491921/5000000000 : ℝ)*X 1 2+(4288346421/10000000000 : ℝ)*X 2 0+(4537973991/10000000000 : ℝ)*X 2 1+(2025491921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28512151098728060925255489/7062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1664451449/50000000000000 : ℝ)*(base19) + (2342487529/100000000000000 : ℝ)*(base23) + (6474959/10000000000000 : ℝ)*(upper3) + (17838103/25000000000000 : ℝ)*(upper4) + (1029710173/100000000000000 : ℝ)*(upper5) + (1628669047352063/50000000000000 : ℝ)*(major0) + (1628669047352063/50000000000000 : ℝ)*(major1) + (1628669047352063/50000000000000 : ℝ)*(major2) + (2241110391324041/50000000000000 : ℝ)*(sp0) + (1120568247189433/25000000000000 : ℝ)*(sp1) + (2241136987586551/50000000000000 : ℝ)*(sp2) + (1016190475734543/50000000000000 : ℝ)*(sp3) + (1110700251/2000000000000 : ℝ)*(sp4) + (9392853949/50000000000000 : ℝ)*(sp7) + (406479947435397/20000000000000 : ℝ)*(f.failure) + (4482276317660631/100000000000000 : ℝ)*(f.sum) + (16340257133257/1483125000000000000000000000 : ℝ)*base65 + (2333178172341453859/197750000000000000000000000000000 : ℝ)*base68 + (3410351227792953859/197750000000000000000000000000000 : ℝ)*base70 + (1870039248417546141/197750000000000000000000000000000 : ℝ)*base71 + (33007344626323/5932500000000000000000000000 : ℝ)*base73 + (49542193878453859/197750000000000000000000000000000 : ℝ)*base76 + (1163615652845453859/197750000000000000000000000000000 : ℝ)*base78 + (1608703914281453859/197750000000000000000000000000000 : ℝ)*base80 + (10077812816527/1483125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (14610571/2000000000000000000000 : ℝ)*base89 + (14610571/2000000000000000000000 : ℝ)*base91 + (14610571/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202745916452399641710080081/49437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24132341/25000000000000 : ℝ)*(base19) + (506688477/100000000000000 : ℝ)*(base23) + (31657309/50000000000000 : ℝ)*(lower2) + (20860719/25000000000000 : ℝ)*(upper3) + (4892203/4000000000000 : ℝ)*(lower4) + (1645522480389661/50000000000000 : ℝ)*(major0) + (1645522480389661/50000000000000 : ℝ)*(major1) + (1645522480389661/50000000000000 : ℝ)*(major2) + (12555948011/100000000000000 : ℝ)*(sp2) + (6265893/25000000000000 : ℝ)*(sp3) + (4528658817957709/100000000000000 : ℝ)*(sp4) + (566082340178543/12500000000000 : ℝ)*(sp5) + (4528645755321221/100000000000000 : ℝ)*(sp6) + (1026715470917759/50000000000000 : ℝ)*(sp7) + (205343096689909/10000000000000 : ℝ)*(f.failure) + (4528658817957709/100000000000000 : ℝ)*(f.sum) + (3712377322937/2966250000000000000000000000 : ℝ)*base66 + (1704561521609002473/197750000000000000000000000000000 : ℝ)*base68 + (280694375596502473/197750000000000000000000000000000 : ℝ)*base70 + (902354936736497527/197750000000000000000000000000000 : ℝ)*base71 + (577448184473/741562500000000000000000000 : ℝ)*base74 + (1139770928011002473/197750000000000000000000000000000 : ℝ)*base76 + (618227334931752473/197750000000000000000000000000000 : ℝ)*base78 + (402874641423002473/197750000000000000000000000000000 : ℝ)*base80 + (7940349474103/2966250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1949413/1000000000000000000000 : ℝ)*base90 + (1949413/1000000000000000000000 : ℝ)*base92 + (1949413/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1473_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1473_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1473_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1473_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1473_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5061/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1473_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
