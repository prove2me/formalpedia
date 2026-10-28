-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:57.821032+00:00
-- url     : https://prove2.me/submissions/b89aaa37-8358-45af-b9f4-5a8936a478ab

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
theorem support_rectangle_w1132_s0_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-47374503/250000000 : ℝ)*x 0 + (18927013/31250000 : ℝ)*x 1 + (477920619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47374503/250000000 : ℝ)^8325 ≤ (11013069009959/100000000000000 : ℝ)^6277 := by
    have hnat : (47374503 : ℕ)^8325*100000000000000^6277 ≤ 11013069009959^6277*250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47374503 250000000 11013069009959 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18927013/31250000 : ℝ)^8325 ≤ (51425769770037/100000000000000 : ℝ)^6277 := by
    have hnat : (18927013 : ℕ)^8325*100000000000000^6277 ≤ 51425769770037^6277*31250000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18927013 31250000 51425769770037 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477920619/1000000000 : ℝ)^8325 ≤ (37561161212973/100000000000000 : ℝ)^6277 := by
    have hnat : (477920619 : ℕ)^8325*100000000000000^6277 ≤ 37561161212973^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477920619 1000000000 37561161212973 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47374503/250000000 : ℝ), (18927013/31250000 : ℝ), (477920619/1000000000 : ℝ)] ![(11013069009959/100000000000000 : ℝ), (51425769770037/100000000000000 : ℝ), (37561161212973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47374503/250000000 : ℝ)|^8325 ≤ (11013069009959/100000000000000 : ℝ)^6277
        have hw : |(-47374503/250000000 : ℝ)|=(47374503/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18927013/31250000 : ℝ)|^8325 ≤ (51425769770037/100000000000000 : ℝ)^6277
        have hw : |(18927013/31250000 : ℝ)|=(18927013/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477920619/1000000000 : ℝ)|^8325 ≤ (37561161212973/100000000000000 : ℝ)^6277
        have hw : |(477920619/1000000000 : ℝ)|=(477920619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103471123/2000000000 : ℝ)*x 0 + (-328545889/1250000000 : ℝ)*x 1 + (1194801689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103471123/2000000000 : ℝ)^8325 ≤ (5680354284537/12500000000000 : ℝ)^6277 := by
    have hnat : (1103471123 : ℕ)^8325*12500000000000^6277 ≤ 5680354284537^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103471123 2000000000 5680354284537 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328545889/1250000000 : ℝ)^8325 ≤ (8497999302053/50000000000000 : ℝ)^6277 := by
    have hnat : (328545889 : ℕ)^8325*50000000000000^6277 ≤ 8497999302053^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328545889 1250000000 8497999302053 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194801689/2500000000 : ℝ)^8325 ≤ (18780583556349/50000000000000 : ℝ)^6277 := by
    have hnat : (1194801689 : ℕ)^8325*50000000000000^6277 ≤ 18780583556349^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194801689 2500000000 18780583556349 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103471123/2000000000 : ℝ), (-328545889/1250000000 : ℝ), (1194801689/2500000000 : ℝ)] ![(5680354284537/12500000000000 : ℝ), (8497999302053/50000000000000 : ℝ), (18780583556349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103471123/2000000000 : ℝ)|^8325 ≤ (5680354284537/12500000000000 : ℝ)^6277
        have hw : |(1103471123/2000000000 : ℝ)|=(1103471123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-328545889/1250000000 : ℝ)|^8325 ≤ (8497999302053/50000000000000 : ℝ)^6277
        have hw : |(-328545889/1250000000 : ℝ)|=(328545889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194801689/2500000000 : ℝ)|^8325 ≤ (18780583556349/50000000000000 : ℝ)^6277
        have hw : |(1194801689/2500000000 : ℝ)|=(1194801689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103471893/2000000000 : ℝ)*x 0 + (955841043/2000000000 : ℝ)*x 1 + (-2628364079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103471893/2000000000 : ℝ)^8325 ≤ (9088575266447/20000000000000 : ℝ)^6277 := by
    have hnat : (1103471893 : ℕ)^8325*20000000000000^6277 ≤ 9088575266447^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103471893 2000000000 9088575266447 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955841043/2000000000 : ℝ)^8325 ≤ (37561151050019/100000000000000 : ℝ)^6277 := by
    have hnat : (955841043 : ℕ)^8325*100000000000000^6277 ≤ 37561151050019^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955841043 2000000000 37561151050019 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628364079/10000000000 : ℝ)^8325 ≤ (16995972592623/100000000000000 : ℝ)^6277 := by
    have hnat : (2628364079 : ℕ)^8325*100000000000000^6277 ≤ 16995972592623^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628364079 10000000000 16995972592623 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103471893/2000000000 : ℝ), (955841043/2000000000 : ℝ), (-2628364079/10000000000 : ℝ)] ![(9088575266447/20000000000000 : ℝ), (37561151050019/100000000000000 : ℝ), (16995972592623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103471893/2000000000 : ℝ)|^8325 ≤ (9088575266447/20000000000000 : ℝ)^6277
        have hw : |(1103471893/2000000000 : ℝ)|=(1103471893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(955841043/2000000000 : ℝ)|^8325 ≤ (37561151050019/100000000000000 : ℝ)^6277
        have hw : |(955841043/2000000000 : ℝ)|=(955841043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2628364079/10000000000 : ℝ)|^8325 ≤ (16995972592623/100000000000000 : ℝ)^6277
        have hw : |(-2628364079/10000000000 : ℝ)|=(2628364079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (210090069/500000000 : ℝ)*x 0 + (1560772847/5000000000 : ℝ)*x 1 + (5657992381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210090069/500000000 : ℝ)^8325 ≤ (31664572839757/100000000000000 : ℝ)^6277 := by
    have hnat : (210090069 : ℕ)^8325*100000000000000^6277 ≤ 31664572839757^6277*500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210090069 500000000 31664572839757 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560772847/5000000000 : ℝ)^8325 ≤ (21349978350521/100000000000000 : ℝ)^6277 := by
    have hnat : (1560772847 : ℕ)^8325*100000000000000^6277 ≤ 21349978350521^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560772847 5000000000 21349978350521 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5657992381/10000000000 : ℝ)^8325 ≤ (23492724395481/50000000000000 : ℝ)^6277 := by
    have hnat : (5657992381 : ℕ)^8325*50000000000000^6277 ≤ 23492724395481^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657992381 10000000000 23492724395481 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210090069/500000000 : ℝ), (1560772847/5000000000 : ℝ), (5657992381/10000000000 : ℝ)] ![(31664572839757/100000000000000 : ℝ), (21349978350521/100000000000000 : ℝ), (23492724395481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210090069/500000000 : ℝ)|^8325 ≤ (31664572839757/100000000000000 : ℝ)^6277
        have hw : |(210090069/500000000 : ℝ)|=(210090069/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560772847/5000000000 : ℝ)|^8325 ≤ (21349978350521/100000000000000 : ℝ)^6277
        have hw : |(1560772847/5000000000 : ℝ)|=(1560772847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5657992381/10000000000 : ℝ)|^8325 ≤ (23492724395481/50000000000000 : ℝ)^6277
        have hw : |(5657992381/10000000000 : ℝ)|=(5657992381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-4750387/25000000 : ℝ)*x 0 + (1203041351/2500000000 : ℝ)*x 1 + (1505631793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4750387/25000000 : ℝ)^8325 ≤ (11052972659869/100000000000000 : ℝ)^6277 := by
    have hnat : (4750387 : ℕ)^8325*100000000000000^6277 ≤ 11052972659869^6277*25000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750387 25000000 11052972659869 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203041351/2500000000 : ℝ)^8325 ≤ (18952549452853/50000000000000 : ℝ)^6277 := by
    have hnat : (1203041351 : ℕ)^8325*50000000000000^6277 ≤ 18952549452853^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203041351 2500000000 18952549452853 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1505631793/2500000000 : ℝ)^8325 ≤ (2552096420971/5000000000000 : ℝ)^6277 := by
    have hnat : (1505631793 : ℕ)^8325*5000000000000^6277 ≤ 2552096420971^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505631793 2500000000 2552096420971 5000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4750387/25000000 : ℝ), (1203041351/2500000000 : ℝ), (1505631793/2500000000 : ℝ)] ![(11052972659869/100000000000000 : ℝ), (18952549452853/50000000000000 : ℝ), (2552096420971/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4750387/25000000 : ℝ)|^8325 ≤ (11052972659869/100000000000000 : ℝ)^6277
        have hw : |(-4750387/25000000 : ℝ)|=(4750387/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203041351/2500000000 : ℝ)|^8325 ≤ (18952549452853/50000000000000 : ℝ)^6277
        have hw : |(1203041351/2500000000 : ℝ)|=(1203041351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1505631793/2500000000 : ℝ)|^8325 ≤ (2552096420971/5000000000000 : ℝ)^6277
        have hw : |(1505631793/2500000000 : ℝ)|=(1505631793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034059599/2000000000 : ℝ)*x 0 + (-1385045147/10000000000 : ℝ)*x 1 + (6022527081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034059599/2000000000 : ℝ)^8325 ≤ (41691176887691/100000000000000 : ℝ)^6277 := by
    have hnat : (1034059599 : ℕ)^8325*100000000000000^6277 ≤ 41691176887691^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034059599 2000000000 41691176887691 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385045147/10000000000 : ℝ)^8325 ≤ (7266895706151/100000000000000 : ℝ)^6277 := by
    have hnat : (1385045147 : ℕ)^8325*100000000000000^6277 ≤ 7266895706151^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385045147 10000000000 7266895706151 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6022527081/10000000000 : ℝ)^8325 ≤ (25520963698273/50000000000000 : ℝ)^6277 := by
    have hnat : (6022527081 : ℕ)^8325*50000000000000^6277 ≤ 25520963698273^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022527081 10000000000 25520963698273 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034059599/2000000000 : ℝ), (-1385045147/10000000000 : ℝ), (6022527081/10000000000 : ℝ)] ![(41691176887691/100000000000000 : ℝ), (7266895706151/100000000000000 : ℝ), (25520963698273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034059599/2000000000 : ℝ)|^8325 ≤ (41691176887691/100000000000000 : ℝ)^6277
        have hw : |(1034059599/2000000000 : ℝ)|=(1034059599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1385045147/10000000000 : ℝ)|^8325 ≤ (7266895706151/100000000000000 : ℝ)^6277
        have hw : |(-1385045147/10000000000 : ℝ)|=(1385045147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6022527081/10000000000 : ℝ)|^8325 ≤ (25520963698273/50000000000000 : ℝ)^6277
        have hw : |(6022527081/10000000000 : ℝ)|=(6022527081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (161571813/312500000 : ℝ)*x 0 + (6022527081/10000000000 : ℝ)*x 1 + (-277009023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161571813/312500000 : ℝ)^8325 ≤ (10422794278069/25000000000000 : ℝ)^6277 := by
    have hnat : (161571813 : ℕ)^8325*25000000000000^6277 ≤ 10422794278069^6277*312500000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161571813 312500000 10422794278069 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6022527081/10000000000 : ℝ)^8325 ≤ (25520963698273/50000000000000 : ℝ)^6277 := by
    have hnat : (6022527081 : ℕ)^8325*50000000000000^6277 ≤ 25520963698273^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022527081 10000000000 25520963698273 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277009023/2000000000 : ℝ)^8325 ≤ (3633447741739/50000000000000 : ℝ)^6277 := by
    have hnat : (277009023 : ℕ)^8325*50000000000000^6277 ≤ 3633447741739^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277009023 2000000000 3633447741739 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161571813/312500000 : ℝ), (6022527081/10000000000 : ℝ), (-277009023/2000000000 : ℝ)] ![(10422794278069/25000000000000 : ℝ), (25520963698273/50000000000000 : ℝ), (3633447741739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161571813/312500000 : ℝ)|^8325 ≤ (10422794278069/25000000000000 : ℝ)^6277
        have hw : |(161571813/312500000 : ℝ)|=(161571813/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6022527081/10000000000 : ℝ)|^8325 ≤ (25520963698273/50000000000000 : ℝ)^6277
        have hw : |(6022527081/10000000000 : ℝ)|=(6022527081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277009023/2000000000 : ℝ)|^8325 ≤ (3633447741739/50000000000000 : ℝ)^6277
        have hw : |(-277009023/2000000000 : ℝ)|=(277009023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s0_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (526509553/1250000000 : ℝ)*x 0 + (5592549511/10000000000 : ℝ)*x 1 + (1594644289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526509553/1250000000 : ℝ)^8325 ≤ (1588365493899/5000000000000 : ℝ)^6277 := by
    have hnat : (526509553 : ℕ)^8325*5000000000000^6277 ≤ 1588365493899^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526509553 1250000000 1588365493899 5000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5592549511/10000000000 : ℝ)^8325 ≤ (11566511099103/25000000000000 : ℝ)^6277 := by
    have hnat : (5592549511 : ℕ)^8325*25000000000000^6277 ≤ 11566511099103^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592549511 10000000000 11566511099103 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594644289/5000000000 : ℝ)^8325 ≤ (21966645709499/100000000000000 : ℝ)^6277 := by
    have hnat : (1594644289 : ℕ)^8325*100000000000000^6277 ≤ 21966645709499^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594644289 5000000000 21966645709499 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526509553/1250000000 : ℝ), (5592549511/10000000000 : ℝ), (1594644289/5000000000 : ℝ)] ![(1588365493899/5000000000000 : ℝ), (11566511099103/25000000000000 : ℝ), (21966645709499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526509553/1250000000 : ℝ)|^8325 ≤ (1588365493899/5000000000000 : ℝ)^6277
        have hw : |(526509553/1250000000 : ℝ)|=(526509553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5592549511/10000000000 : ℝ)|^8325 ≤ (11566511099103/25000000000000 : ℝ)^6277
        have hw : |(5592549511/10000000000 : ℝ)|=(5592549511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594644289/5000000000 : ℝ)|^8325 ≤ (21966645709499/100000000000000 : ℝ)^6277
        have hw : |(1594644289/5000000000 : ℝ)|=(1594644289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (93/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27853/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (2081/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2081 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2081*1^512 ≤ 0^512*1^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2081/512 : ℝ) ≤ (1206594920018576461/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2081 ≤ (1206594920018576461/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2081*50000000000000000000^512 ≤ 1206594920018576461^512*5^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1206594920018576461 50000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1206594920018576461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2081 := by
      have hnat : (1 : ℕ)^512*1^2081 ≤ 1^2081*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51206594920018576461/50000000000000000000 : ℝ) ≤ (1257355051670721/1250000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (51206594920018576461/50000000000000000000 : ℝ)^512 ≤ (1257355051670721/1250000000000000 : ℝ)^2081 := by
      have hnat : (51206594920018576461 : ℕ)^512*1250000000000000^2081 ≤ 1257355051670721^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51206594920018576461 50000000000000000000 1257355051670721 1250000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257355051670721/1250000000000000 : ℝ)) (X := (51206594920018576461/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26206594920018576461/25000000000000000000 : ℝ) ≤ (632355051670721/625000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (26206594920018576461/25000000000000000000 : ℝ)^512 ≤ (632355051670721/625000000000000 : ℝ)^2081 := by
      have hnat : (26206594920018576461 : ℕ)^512*625000000000000^2081 ≤ 632355051670721^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26206594920018576461 25000000000000000000 632355051670721 625000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632355051670721/625000000000000 : ℝ)) (X := (26206594920018576461/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7355051670721/500000000000000 : ℝ)*(0 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(7355051670721/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1206594920018576461/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7355051670721/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (1 : ℝ)+(7355051670721/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257355051670721/1250000000000000 : ℝ) by norm_num, show 1+(1206594920018576461/50000000000000000000 : ℝ)+(0 : ℝ)=(51206594920018576461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1206594920018576461/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7355051670721/500000000000000 : ℝ)*(2/5 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(7355051670721/500000000000000 : ℝ)*(2/5 : ℝ)=(632355051670721/625000000000000 : ℝ) by norm_num, show 1+2*(1206594920018576461/50000000000000000000 : ℝ)=(26206594920018576461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7355051670721/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7355051670721/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7355051670721/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7355051670721/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7355051670721/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7355051670721/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-47374503/250000000 : ℝ)*X 0 0+(18927013/31250000 : ℝ)*X 0 1+(477920619/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103471123/2000000000 : ℝ)*X 1 0+(-328545889/1250000000 : ℝ)*X 1 1+(1194801689/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103471893/2000000000 : ℝ)*X 2 0+(955841043/2000000000 : ℝ)*X 2 1+(-2628364079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((210090069/500000000 : ℝ)*X 0 0+(1560772847/5000000000 : ℝ)*X 0 1+(5657992381/10000000000 : ℝ)*X 0 2+(210090069/500000000 : ℝ)*X 1 0+(1560772847/5000000000 : ℝ)*X 1 1+(5657992381/10000000000 : ℝ)*X 1 2+(210090069/500000000 : ℝ)*X 2 0+(1560772847/5000000000 : ℝ)*X 2 1+(5657992381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4750387/25000000 : ℝ)*X 0 0+(1203041351/2500000000 : ℝ)*X 0 1+(1505631793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034059599/2000000000 : ℝ)*X 1 0+(-1385045147/10000000000 : ℝ)*X 1 1+(6022527081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((161571813/312500000 : ℝ)*X 2 0+(6022527081/10000000000 : ℝ)*X 2 1+(-277009023/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((526509553/1250000000 : ℝ)*X 0 0+(5592549511/10000000000 : ℝ)*X 0 1+(1594644289/5000000000 : ℝ)*X 0 2+(526509553/1250000000 : ℝ)*X 1 0+(5592549511/10000000000 : ℝ)*X 1 1+(1594644289/5000000000 : ℝ)*X 1 2+(526509553/1250000000 : ℝ)*X 2 0+(5592549511/10000000000 : ℝ)*X 2 1+(1594644289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16174513433200465536621/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (901959/2000000000000 : ℝ)*(base1) + (1416233237/100000000000000 : ℝ)*(base19) + (789205047/50000000000000 : ℝ)*(base23) + (76814987/20000000000000 : ℝ)*(base24) + (74197003/20000000000000 : ℝ)*(upper3) + (73567531686533/12500000000000 : ℝ)*(major0) + (73567531686533/12500000000000 : ℝ)*(major1) + (73567531686533/12500000000000 : ℝ)*(major2) + (78282104179571/10000000000000 : ℝ)*(sp0) + (24463210203751/3125000000000 : ℝ)*(sp1) + (782822180268239/100000000000000 : ℝ)*(sp2) + (197126719372571/50000000000000 : ℝ)*(sp3) + (786513877/25000000000000 : ℝ)*(sp4) + (2707860019/100000000000000 : ℝ)*(sp7) + (394256191703111/100000000000000 : ℝ)*(f.failure) + (195706035688317/25000000000000 : ℝ)*(f.sum) + (3170445199707/3125000000000000000000000000 : ℝ)*base66 + (20684643044043/6250000000000000000000000000 : ℝ)*base67 + (38685791350293/6250000000000000000000000000 : ℝ)*base69 + (828708000293/6250000000000000000000000000 : ℝ)*base71 + (32386609729/390625000000000000000000000 : ℝ)*base74 + (22601883124707/6250000000000000000000000000 : ℝ)*base76 + (21326505156543/6250000000000000000000000000 : ℝ)*base77 + (18297970837793/6250000000000000000000000000 : ℝ)*base79 + (3755285545459/1562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (48072737/10000000000000000000000 : ℝ)*base90 + (48072737/10000000000000000000000 : ℝ)*base92 + (48072737/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20814153813863457032481/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14745341/50000000000000 : ℝ)*(base1) + (50076911/12500000000000 : ℝ)*(base19) + (201570061/50000000000000 : ℝ)*(base23) + (7669223/20000000000000 : ℝ)*(upper3) + (50142859/100000000000000 : ℝ)*(upper5) + (621150332401229/100000000000000 : ℝ)*(major0) + (621150332401229/100000000000000 : ℝ)*(major1) + (621150332401229/100000000000000 : ℝ)*(major2) + (384930063/50000000000000 : ℝ)*(sp1) + (757473331/100000000000000 : ℝ)*(sp2) + (826199338878489/100000000000000 : ℝ)*(sp4) + (413099069456197/50000000000000 : ℝ)*(sp5) + (165239629754871/20000000000000 : ℝ)*(sp6) + (208050635209777/50000000000000 : ℝ)*(sp7) + (83220259982047/20000000000000 : ℝ)*(f.failure) + (25818728418369/3125000000000 : ℝ)*(f.sum) + (48691278683891/25000000000000000000000000000 : ℝ)*base66 + (56800468783891/50000000000000000000000000000 : ℝ)*base68 + (78586702283891/50000000000000000000000000000 : ℝ)*base70 + (92221457083891/50000000000000000000000000000 : ℝ)*base72 + (93671587883891/25000000000000000000000000000 : ℝ)*base74 + (183434205383891/50000000000000000000000000000 : ℝ)*base76 + (174048960833891/50000000000000000000000000000 : ℝ)*base78 + (394742186983891/50000000000000000000000000000 : ℝ)*base80 + (66372617233891/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (701751/2000000000000000000000 : ℝ)*base89 + (701751/2000000000000000000000 : ℝ)*base91 + (701751/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1132_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (93/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27853/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_s1_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100372267/10000000000 : ℝ)*x 0 + (5704179977/10000000000 : ℝ)*x 1 + (625021793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100372267/10000000000 : ℝ)^8325 ≤ (12623550869171/100000000000000 : ℝ)^6277 := by
    have hnat : (2100372267 : ℕ)^8325*100000000000000^6277 ≤ 12623550869171^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100372267 10000000000 12623550869171 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704179977/10000000000 : ℝ)^8325 ≤ (9498964238101/20000000000000 : ℝ)^6277 := by
    have hnat : (5704179977 : ℕ)^8325*20000000000000^6277 ≤ 9498964238101^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704179977 10000000000 9498964238101 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625021793/1250000000 : ℝ)^8325 ≤ (99704069829/250000000000 : ℝ)^6277 := by
    have hnat : (625021793 : ℕ)^8325*250000000000^6277 ≤ 99704069829^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625021793 1250000000 99704069829 250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100372267/10000000000 : ℝ), (5704179977/10000000000 : ℝ), (625021793/1250000000 : ℝ)] ![(12623550869171/100000000000000 : ℝ), (9498964238101/20000000000000 : ℝ), (99704069829/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100372267/10000000000 : ℝ)|^8325 ≤ (12623550869171/100000000000000 : ℝ)^6277
        have hw : |(-2100372267/10000000000 : ℝ)|=(2100372267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704179977/10000000000 : ℝ)|^8325 ≤ (9498964238101/20000000000000 : ℝ)^6277
        have hw : |(5704179977/10000000000 : ℝ)|=(5704179977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(625021793/1250000000 : ℝ)|^8325 ≤ (99704069829/250000000000 : ℝ)^6277
        have hw : |(625021793/1250000000 : ℝ)|=(625021793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5419669143/10000000000 : ℝ)*x 0 + (-2480485997/10000000000 : ℝ)*x 1 + (625021733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419669143/10000000000 : ℝ)^8325 ≤ (44378838953167/100000000000000 : ℝ)^6277 := by
    have hnat : (5419669143 : ℕ)^8325*100000000000000^6277 ≤ 44378838953167^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419669143 10000000000 44378838953167 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2480485997/10000000000 : ℝ)^8325 ≤ (15739538170679/100000000000000 : ℝ)^6277 := by
    have hnat : (2480485997 : ℕ)^8325*100000000000000^6277 ≤ 15739538170679^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480485997 10000000000 15739538170679 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625021733/1250000000 : ℝ)^8325 ≤ (39881622853969/100000000000000 : ℝ)^6277 := by
    have hnat : (625021733 : ℕ)^8325*100000000000000^6277 ≤ 39881622853969^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625021733 1250000000 39881622853969 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5419669143/10000000000 : ℝ), (-2480485997/10000000000 : ℝ), (625021733/1250000000 : ℝ)] ![(44378838953167/100000000000000 : ℝ), (15739538170679/100000000000000 : ℝ), (39881622853969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5419669143/10000000000 : ℝ)|^8325 ≤ (44378838953167/100000000000000 : ℝ)^6277
        have hw : |(5419669143/10000000000 : ℝ)|=(5419669143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2480485997/10000000000 : ℝ)|^8325 ≤ (15739538170679/100000000000000 : ℝ)^6277
        have hw : |(-2480485997/10000000000 : ℝ)|=(2480485997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(625021733/1250000000 : ℝ)|^8325 ≤ (39881622853969/100000000000000 : ℝ)^6277
        have hw : |(625021733/1250000000 : ℝ)|=(625021733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083934181/2000000000 : ℝ)*x 0 + (1250043071/2500000000 : ℝ)*x 1 + (-248048571/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083934181/2000000000 : ℝ)^8325 ≤ (5547357261091/12500000000000 : ℝ)^6277 := by
    have hnat : (1083934181 : ℕ)^8325*12500000000000^6277 ≤ 5547357261091^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083934181 2000000000 5547357261091 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250043071/2500000000 : ℝ)^8325 ≤ (4985200767513/12500000000000 : ℝ)^6277 := by
    have hnat : (1250043071 : ℕ)^8325*12500000000000^6277 ≤ 4985200767513^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250043071 2500000000 4985200767513 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248048571/1000000000 : ℝ)^8325 ≤ (15739535755389/100000000000000 : ℝ)^6277 := by
    have hnat : (248048571 : ℕ)^8325*100000000000000^6277 ≤ 15739535755389^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248048571 1000000000 15739535755389 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083934181/2000000000 : ℝ), (1250043071/2500000000 : ℝ), (-248048571/1000000000 : ℝ)] ![(5547357261091/12500000000000 : ℝ), (4985200767513/12500000000000 : ℝ), (15739535755389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083934181/2000000000 : ℝ)|^8325 ≤ (5547357261091/12500000000000 : ℝ)^6277
        have hw : |(1083934181/2000000000 : ℝ)|=(1083934181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250043071/2500000000 : ℝ)|^8325 ≤ (4985200767513/12500000000000 : ℝ)^6277
        have hw : |(1250043071/2500000000 : ℝ)|=(1250043071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248048571/1000000000 : ℝ)|^8325 ≤ (15739535755389/100000000000000 : ℝ)^6277
        have hw : |(-248048571/1000000000 : ℝ)|=(248048571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (863657263/2000000000 : ℝ)*x 0 + (3675171459/10000000000 : ℝ)*x 1 + (634127953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863657263/2000000000 : ℝ)^8325 ≤ (8208509736749/25000000000000 : ℝ)^6277 := by
    have hnat : (863657263 : ℕ)^8325*25000000000000^6277 ≤ 8208509736749^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863657263 2000000000 8208509736749 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3675171459/10000000000 : ℝ)^8325 ≤ (26511878886659/100000000000000 : ℝ)^6277 := by
    have hnat : (3675171459 : ℕ)^8325*100000000000000^6277 ≤ 26511878886659^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3675171459 10000000000 26511878886659 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634127953/1250000000 : ℝ)^8325 ≤ (40654082157973/100000000000000 : ℝ)^6277 := by
    have hnat : (634127953 : ℕ)^8325*100000000000000^6277 ≤ 40654082157973^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634127953 1250000000 40654082157973 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863657263/2000000000 : ℝ), (3675171459/10000000000 : ℝ), (634127953/1250000000 : ℝ)] ![(8208509736749/25000000000000 : ℝ), (26511878886659/100000000000000 : ℝ), (40654082157973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863657263/2000000000 : ℝ)|^8325 ≤ (8208509736749/25000000000000 : ℝ)^6277
        have hw : |(863657263/2000000000 : ℝ)|=(863657263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3675171459/10000000000 : ℝ)|^8325 ≤ (26511878886659/100000000000000 : ℝ)^6277
        have hw : |(3675171459/10000000000 : ℝ)|=(3675171459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634127953/1250000000 : ℝ)|^8325 ≤ (40654082157973/100000000000000 : ℝ)^6277
        have hw : |(634127953/1250000000 : ℝ)|=(634127953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101192631/10000000000 : ℝ)*x 0 + (2504911687/5000000000 : ℝ)*x 1 + (1138867797/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101192631/10000000000 : ℝ)^8325 ≤ (789380654747/6250000000000 : ℝ)^6277 := by
    have hnat : (2101192631 : ℕ)^8325*6250000000000^6277 ≤ 789380654747^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101192631 10000000000 789380654747 6250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504911687/5000000000 : ℝ)^8325 ≤ (39983731316323/100000000000000 : ℝ)^6277 := by
    have hnat : (2504911687 : ℕ)^8325*100000000000000^6277 ≤ 39983731316323^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504911687 5000000000 39983731316323 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138867797/2000000000 : ℝ)^8325 ≤ (47386178194159/100000000000000 : ℝ)^6277 := by
    have hnat : (1138867797 : ℕ)^8325*100000000000000^6277 ≤ 47386178194159^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138867797 2000000000 47386178194159 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101192631/10000000000 : ℝ), (2504911687/5000000000 : ℝ), (1138867797/2000000000 : ℝ)] ![(789380654747/6250000000000 : ℝ), (39983731316323/100000000000000 : ℝ), (47386178194159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101192631/10000000000 : ℝ)|^8325 ≤ (789380654747/6250000000000 : ℝ)^6277
        have hw : |(-2101192631/10000000000 : ℝ)|=(2101192631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2504911687/5000000000 : ℝ)|^8325 ≤ (39983731316323/100000000000000 : ℝ)^6277
        have hw : |(2504911687/5000000000 : ℝ)|=(2504911687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1138867797/2000000000 : ℝ)|^8325 ≤ (47386178194159/100000000000000 : ℝ)^6277
        have hw : |(1138867797/2000000000 : ℝ)|=(1138867797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309816471/2500000000 : ℝ)*x 0 + (-893160267/5000000000 : ℝ)*x 1 + (569433871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309816471/2500000000 : ℝ)^8325 ≤ (42430354593179/100000000000000 : ℝ)^6277 := by
    have hnat : (1309816471 : ℕ)^8325*100000000000000^6277 ≤ 42430354593179^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309816471 2500000000 42430354593179 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893160267/5000000000 : ℝ)^8325 ≤ (2545867558717/25000000000000 : ℝ)^6277 := by
    have hnat : (893160267 : ℕ)^8325*25000000000000^6277 ≤ 2545867558717^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893160267 5000000000 2545867558717 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569433871/1000000000 : ℝ)^8325 ≤ (23693087579529/50000000000000 : ℝ)^6277 := by
    have hnat : (569433871 : ℕ)^8325*50000000000000^6277 ≤ 23693087579529^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569433871 1000000000 23693087579529 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309816471/2500000000 : ℝ), (-893160267/5000000000 : ℝ), (569433871/1000000000 : ℝ)] ![(42430354593179/100000000000000 : ℝ), (2545867558717/25000000000000 : ℝ), (23693087579529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309816471/2500000000 : ℝ)|^8325 ≤ (42430354593179/100000000000000 : ℝ)^6277
        have hw : |(1309816471/2500000000 : ℝ)|=(1309816471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893160267/5000000000 : ℝ)|^8325 ≤ (2545867558717/25000000000000 : ℝ)^6277
        have hw : |(-893160267/5000000000 : ℝ)|=(893160267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569433871/1000000000 : ℝ)|^8325 ≤ (23693087579529/50000000000000 : ℝ)^6277
        have hw : |(569433871/1000000000 : ℝ)|=(569433871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239265931/10000000000 : ℝ)*x 0 + (2847169443/5000000000 : ℝ)*x 1 + (-1786320209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239265931/10000000000 : ℝ)^8325 ≤ (21215177548999/50000000000000 : ℝ)^6277 := by
    have hnat : (5239265931 : ℕ)^8325*50000000000000^6277 ≤ 21215177548999^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239265931 10000000000 21215177548999 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2847169443/5000000000 : ℝ)^8325 ≤ (47386177101523/100000000000000 : ℝ)^6277 := by
    have hnat : (2847169443 : ℕ)^8325*100000000000000^6277 ≤ 47386177101523^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847169443 5000000000 47386177101523 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1786320209/10000000000 : ℝ)^8325 ≤ (2545866944401/25000000000000 : ℝ)^6277 := by
    have hnat : (1786320209 : ℕ)^8325*25000000000000^6277 ≤ 2545866944401^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786320209 10000000000 2545866944401 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239265931/10000000000 : ℝ), (2847169443/5000000000 : ℝ), (-1786320209/10000000000 : ℝ)] ![(21215177548999/50000000000000 : ℝ), (47386177101523/100000000000000 : ℝ), (2545866944401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239265931/10000000000 : ℝ)|^8325 ≤ (21215177548999/50000000000000 : ℝ)^6277
        have hw : |(5239265931/10000000000 : ℝ)|=(5239265931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2847169443/5000000000 : ℝ)|^8325 ≤ (47386177101523/100000000000000 : ℝ)^6277
        have hw : |(2847169443/5000000000 : ℝ)|=(2847169443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1786320209/10000000000 : ℝ)|^8325 ≤ (2545866944401/25000000000000 : ℝ)^6277
        have hw : |(-1786320209/10000000000 : ℝ)|=(1786320209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s1_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319912013/10000000000 : ℝ)*x 0 + (5053865677/10000000000 : ℝ)*x 1 + (923677579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319912013/10000000000 : ℝ)^8325 ≤ (16425216975541/50000000000000 : ℝ)^6277 := by
    have hnat : (4319912013 : ℕ)^8325*50000000000000^6277 ≤ 16425216975541^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319912013 10000000000 16425216975541 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5053865677/10000000000 : ℝ)^8325 ≤ (8090117736313/20000000000000 : ℝ)^6277 := by
    have hnat : (5053865677 : ℕ)^8325*20000000000000^6277 ≤ 8090117736313^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053865677 10000000000 8090117736313 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923677579/2500000000 : ℝ)^8325 ≤ (13349488675283/50000000000000 : ℝ)^6277 := by
    have hnat : (923677579 : ℕ)^8325*50000000000000^6277 ≤ 13349488675283^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923677579 2500000000 13349488675283 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319912013/10000000000 : ℝ), (5053865677/10000000000 : ℝ), (923677579/2500000000 : ℝ)] ![(16425216975541/50000000000000 : ℝ), (8090117736313/20000000000000 : ℝ), (13349488675283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319912013/10000000000 : ℝ)|^8325 ≤ (16425216975541/50000000000000 : ℝ)^6277
        have hw : |(4319912013/10000000000 : ℝ)|=(4319912013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5053865677/10000000000 : ℝ)|^8325 ≤ (8090117736313/20000000000000 : ℝ)^6277
        have hw : |(5053865677/10000000000 : ℝ)|=(5053865677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923677579/2500000000 : ℝ)|^8325 ≤ (13349488675283/50000000000000 : ℝ)^6277
        have hw : |(923677579/2500000000 : ℝ)|=(923677579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (93/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10241/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (93/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (93/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (93/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (93/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (93/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (93/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (93/25000 : ℝ) ^ (2081/512 : ℝ) ≤ (6676604707/50000000000000000000 : ℝ) := by
    have hpowers : (93/25000 : ℝ)^2081 ≤ (6676604707/50000000000000000000 : ℝ)^512 := by
      have hnat : (93 : ℕ)^2081*50000000000000000000^512 ≤ 6676604707^512*25000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93 25000 6676604707 50000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93/25000 : ℝ)) (X := (6676604707/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27853/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (6928164548801459/1250000000000000000 : ℝ) := by
    have hpowers : (27853/100000 : ℝ)^2081 ≤ (6928164548801459/1250000000000000000 : ℝ)^512 := by
      have hnat : (27853 : ℕ)^2081*1250000000000000000^512 ≤ 6928164548801459^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27853 100000 6928164548801459 1250000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27853/100000 : ℝ)) (X := (6928164548801459/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000006676604707/25000000000000000000 : ℝ) ≤ (10000000000657073/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (25000000006676604707/25000000000000000000 : ℝ)^512 ≤ (10000000000657073/10000000000000000 : ℝ)^2081 := by
      have hnat : (25000000006676604707 : ℕ)^512*10000000000000000^2081 ≤ 10000000000657073^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000006676604707 25000000000000000000 10000000000657073 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000657073/10000000000000000 : ℝ)) (X := (25000000006676604707/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50277126588628663067/50000000000000000000 : ℝ) ≤ (10013608198254269/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50277126588628663067/50000000000000000000 : ℝ)^512 ≤ (10013608198254269/10000000000000000 : ℝ)^2081 := by
      have hnat : (50277126588628663067 : ℕ)^512*10000000000000000^2081 ≤ 10013608198254269^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50277126588628663067 50000000000000000000 10013608198254269 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013608198254269/10000000000000000 : ℝ)) (X := (50277126588628663067/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (631928164548801459/625000000000000000 : ℝ) ≤ (2005443279170293/2000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (631928164548801459/625000000000000000 : ℝ)^512 ≤ (2005443279170293/2000000000000000 : ℝ)^2081 := by
      have hnat : (631928164548801459 : ℕ)^512*2000000000000000^2081 ≤ 2005443279170293^2081*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        631928164548801459 625000000000000000 2005443279170293 2000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005443279170293/2000000000000000 : ℝ)) (X := (631928164548801459/625000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6676604707/50000000000000000000 : ℝ) ≤ ((274799875519044709289/274810000000000000000 : ℝ)+2*(3402049399299/687025000000000 : ℝ)*(93/25000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (274799875519044709289/274810000000000000000 : ℝ)+2*(3402049399299/687025000000000 : ℝ)*(93/25000 : ℝ)=(10000000000657073/10000000000000000 : ℝ) by norm_num, show 1+2*(6676604707/50000000000000000000 : ℝ)=(25000000006676604707/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6928164548801459/1250000000000000000 : ℝ)+(6676604707/50000000000000000000 : ℝ) ≤ ((274799875519044709289/274810000000000000000 : ℝ)+(3402049399299/687025000000000 : ℝ)*((27853/100000 : ℝ)+(93/25000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (274799875519044709289/274810000000000000000 : ℝ)+(3402049399299/687025000000000 : ℝ)*((27853/100000 : ℝ)+(93/25000 : ℝ))=(10013608198254269/10000000000000000 : ℝ) by norm_num, show 1+(6928164548801459/1250000000000000000 : ℝ)+(6676604707/50000000000000000000 : ℝ)=(50277126588628663067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6928164548801459/1250000000000000000 : ℝ) ≤ ((274799875519044709289/274810000000000000000 : ℝ)+2*(3402049399299/687025000000000 : ℝ)*(27853/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (274799875519044709289/274810000000000000000 : ℝ)+2*(3402049399299/687025000000000 : ℝ)*(27853/100000 : ℝ)=(2005443279170293/2000000000000000 : ℝ) by norm_num, show 1+2*(6928164548801459/1250000000000000000 : ℝ)=(631928164548801459/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (274799875519044709289/274810000000000000000 : ℝ)*(X 1 0+X 2 0)+(3402049399299/687025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (93/25000 : ℝ)) (hi := (27853/100000 : ℝ)) (c := (274799875519044709289/274810000000000000000 : ℝ)) (alpha := (3402049399299/687025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (274799875519044709289/274810000000000000000 : ℝ)*(X 0 1+X 2 1)+(3402049399299/687025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (93/25000 : ℝ)) (hi := (27853/100000 : ℝ)) (c := (274799875519044709289/274810000000000000000 : ℝ)) (alpha := (3402049399299/687025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (274799875519044709289/274810000000000000000 : ℝ)*(X 0 2+X 1 2)+(3402049399299/687025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (93/25000 : ℝ)) (hi := (27853/100000 : ℝ)) (c := (274799875519044709289/274810000000000000000 : ℝ)) (alpha := (3402049399299/687025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2100372267/10000000000 : ℝ)*X 0 0+(5704179977/10000000000 : ℝ)*X 0 1+(625021793/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5419669143/10000000000 : ℝ)*X 1 0+(-2480485997/10000000000 : ℝ)*X 1 1+(625021733/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083934181/2000000000 : ℝ)*X 2 0+(1250043071/2500000000 : ℝ)*X 2 1+(-248048571/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863657263/2000000000 : ℝ)*X 0 0+(3675171459/10000000000 : ℝ)*X 0 1+(634127953/1250000000 : ℝ)*X 0 2+(863657263/2000000000 : ℝ)*X 1 0+(3675171459/10000000000 : ℝ)*X 1 1+(634127953/1250000000 : ℝ)*X 1 2+(863657263/2000000000 : ℝ)*X 2 0+(3675171459/10000000000 : ℝ)*X 2 1+(634127953/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2101192631/10000000000 : ℝ)*X 0 0+(2504911687/5000000000 : ℝ)*X 0 1+(1138867797/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309816471/2500000000 : ℝ)*X 1 0+(-893160267/5000000000 : ℝ)*X 1 1+(569433871/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239265931/10000000000 : ℝ)*X 2 0+(2847169443/5000000000 : ℝ)*X 2 1+(-1786320209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319912013/10000000000 : ℝ)*X 0 0+(5053865677/10000000000 : ℝ)*X 0 1+(923677579/2500000000 : ℝ)*X 0 2+(4319912013/10000000000 : ℝ)*X 1 0+(5053865677/10000000000 : ℝ)*X 1 1+(923677579/2500000000 : ℝ)*X 1 2+(4319912013/10000000000 : ℝ)*X 2 0+(5053865677/10000000000 : ℝ)*X 2 1+(923677579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127901587744573028039279400153/13740500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116763507/25000000000000 : ℝ)*(base1) + (1671544667/100000000000000 : ℝ)*(base19) + (266668837/12500000000000 : ℝ)*(base23) + (8480557/25000000000000 : ℝ)*(upper3) + (258160131/100000000000000 : ℝ)*(upper5) + (1067920889510647/100000000000000 : ℝ)*(major0) + (1067920889510647/100000000000000 : ℝ)*(major1) + (1067920889510647/100000000000000 : ℝ)*(major2) + (71022354574163/5000000000000 : ℝ)*(sp0) + (710226078643213/50000000000000 : ℝ)*(sp1) + (1420451695480397/100000000000000 : ℝ)*(sp2) + (357692712440149/50000000000000 : ℝ)*(sp3) + (7204401861/100000000000000 : ℝ)*(sp4) + (1747977037/100000000000000 : ℝ)*(sp7) + (178846909977841/25000000000000 : ℝ)*(f.failure) + (1420453828831093/100000000000000 : ℝ)*(f.sum) + (130056886939153/34351250000000000000000000000 : ℝ)*base65 + (237061536208101499983/27481000000000000000000000000000000 : ℝ)*base67 + (20990846265877499983/27481000000000000000000000000000000 : ℝ)*base69 + (232245150083777499983/27481000000000000000000000000000000 : ℝ)*base71 + (477361795083667/137405000000000000000000000000 : ℝ)*base73 + (125670439856618499983/27481000000000000000000000000000000 : ℝ)*base75 + (176904012122250499983/27481000000000000000000000000000000 : ℝ)*base77 + (201469994094667499983/27481000000000000000000000000000000 : ℝ)*base79 + (5161427567829/68702500000000000000000000000 : ℝ)*base82 + (10228647/2500000000000000000000 : ℝ)*base90 + (10228647/2500000000000000000000 : ℝ)*base92 + (10228647/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3127813311715398163117083129/1717562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15060857/50000000000000 : ℝ)*(base1) + (215696059/50000000000000 : ℝ)*(base19) + (466409641/100000000000000 : ℝ)*(base23) + (27672461/100000000000000 : ℝ)*(upper3) + (36231801/100000000000000 : ℝ)*(upper5) + (137289897911271/12500000000000 : ℝ)*(major0) + (137289897911271/12500000000000 : ℝ)*(major1) + (137289897911271/12500000000000 : ℝ)*(major2) + (1451292877/100000000000000 : ℝ)*(sp1) + (1043824883/50000000000000 : ℝ)*(sp2) + (730443618358899/50000000000000 : ℝ)*(sp4) + (91305332744443/6250000000000 : ℝ)*(sp5) + (1460884652536677/100000000000000 : ℝ)*(sp6) + (735751069159967/100000000000000 : ℝ)*(sp7) + (367875549640841/50000000000000 : ℝ)*(f.failure) + (365221801649021/25000000000000 : ℝ)*(f.sum) + (226909053649563/137405000000000000000000000000 : ℝ)*base65 + (33359704664949221319/3435125000000000000000000000000000 : ℝ)*base67 + (17846984204427846319/3435125000000000000000000000000000 : ℝ)*base69 + (30887662772961346319/3435125000000000000000000000000000 : ℝ)*base71 + (227714254691119/68702500000000000000000000000 : ℝ)*base73 + (21328043084475596319/3435125000000000000000000000000000 : ℝ)*base75 + (12289918990207096319/3435125000000000000000000000000000 : ℝ)*base77 + (27958324715744971319/3435125000000000000000000000000000 : ℝ)*base79 + (152965369272767/137405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (14549647/5000000000000000000000 : ℝ)*base90 + (14549647/5000000000000000000000 : ℝ)*base92 + (14549647/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1132_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (93/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10241/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_s2_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-86165737/400000000 : ℝ)*x 0 + (2756356859/5000000000 : ℝ)*x 1 + (1031491689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86165737/400000000 : ℝ)^8325 ≤ (1631743143879/12500000000000 : ℝ)^6277 := by
    have hnat : (86165737 : ℕ)^8325*12500000000000^6277 ≤ 1631743143879^6277*400000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86165737 400000000 1631743143879 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756356859/5000000000 : ℝ)^8325 ≤ (45392134922427/100000000000000 : ℝ)^6277 := by
    have hnat : (2756356859 : ℕ)^8325*100000000000000^6277 ≤ 45392134922427^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756356859 5000000000 45392134922427 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031491689/2000000000 : ℝ)^8325 ≤ (41553919913141/100000000000000 : ℝ)^6277 := by
    have hnat : (1031491689 : ℕ)^8325*100000000000000^6277 ≤ 41553919913141^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031491689 2000000000 41553919913141 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86165737/400000000 : ℝ), (2756356859/5000000000 : ℝ), (1031491689/2000000000 : ℝ)] ![(1631743143879/12500000000000 : ℝ), (45392134922427/100000000000000 : ℝ), (41553919913141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86165737/400000000 : ℝ)|^8325 ≤ (1631743143879/12500000000000 : ℝ)^6277
        have hw : |(-86165737/400000000 : ℝ)|=(86165737/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756356859/5000000000 : ℝ)|^8325 ≤ (45392134922427/100000000000000 : ℝ)^6277
        have hw : |(2756356859/5000000000 : ℝ)|=(2756356859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031491689/2000000000 : ℝ)|^8325 ≤ (41553919913141/100000000000000 : ℝ)^6277
        have hw : |(1031491689/2000000000 : ℝ)|=(1031491689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687145987/5000000000 : ℝ)*x 0 + (-2338913097/10000000000 : ℝ)*x 1 + (5157460213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687145987/5000000000 : ℝ)^8325 ≤ (43886711092943/100000000000000 : ℝ)^6277 := by
    have hnat : (2687145987 : ℕ)^8325*100000000000000^6277 ≤ 43886711092943^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687145987 5000000000 43886711092943 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2338913097/10000000000 : ℝ)^8325 ≤ (14559350082359/100000000000000 : ℝ)^6277 := by
    have hnat : (2338913097 : ℕ)^8325*100000000000000^6277 ≤ 14559350082359^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338913097 10000000000 14559350082359 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5157460213/10000000000 : ℝ)^8325 ≤ (20776969402847/50000000000000 : ℝ)^6277 := by
    have hnat : (5157460213 : ℕ)^8325*50000000000000^6277 ≤ 20776969402847^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157460213 10000000000 20776969402847 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687145987/5000000000 : ℝ), (-2338913097/10000000000 : ℝ), (5157460213/10000000000 : ℝ)] ![(43886711092943/100000000000000 : ℝ), (14559350082359/100000000000000 : ℝ), (20776969402847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687145987/5000000000 : ℝ)|^8325 ≤ (43886711092943/100000000000000 : ℝ)^6277
        have hw : |(2687145987/5000000000 : ℝ)|=(2687145987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2338913097/10000000000 : ℝ)|^8325 ≤ (14559350082359/100000000000000 : ℝ)^6277
        have hw : |(-2338913097/10000000000 : ℝ)|=(2338913097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5157460213/10000000000 : ℝ)|^8325 ≤ (20776969402847/50000000000000 : ℝ)^6277
        have hw : |(5157460213/10000000000 : ℝ)|=(5157460213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1074858381/2000000000 : ℝ)*x 0 + (2578730103/5000000000 : ℝ)*x 1 + (-2338913197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074858381/2000000000 : ℝ)^8325 ≤ (43886710345647/100000000000000 : ℝ)^6277 := by
    have hnat : (1074858381 : ℕ)^8325*100000000000000^6277 ≤ 43886710345647^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074858381 2000000000 43886710345647 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2578730103/5000000000 : ℝ)^8325 ≤ (20776969365447/50000000000000 : ℝ)^6277 := by
    have hnat : (2578730103 : ℕ)^8325*50000000000000^6277 ≤ 20776969365447^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578730103 5000000000 20776969365447 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2338913197/10000000000 : ℝ)^8325 ≤ (727967545397/5000000000000 : ℝ)^6277 := by
    have hnat : (2338913197 : ℕ)^8325*5000000000000^6277 ≤ 727967545397^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338913197 10000000000 727967545397 5000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074858381/2000000000 : ℝ), (2578730103/5000000000 : ℝ), (-2338913197/10000000000 : ℝ)] ![(43886710345647/100000000000000 : ℝ), (20776969365447/50000000000000 : ℝ), (727967545397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074858381/2000000000 : ℝ)|^8325 ≤ (43886710345647/100000000000000 : ℝ)^6277
        have hw : |(1074858381/2000000000 : ℝ)|=(1074858381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2578730103/5000000000 : ℝ)|^8325 ≤ (20776969365447/50000000000000 : ℝ)^6277
        have hw : |(2578730103/5000000000 : ℝ)|=(2578730103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2338913197/10000000000 : ℝ)|^8325 ≤ (727967545397/5000000000000 : ℝ)^6277
        have hw : |(-2338913197/10000000000 : ℝ)|=(2338913197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435514921/1000000000 : ℝ)*x 0 + (4016643849/10000000000 : ℝ)*x 1 + (47220247/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435514921/1000000000 : ℝ)^8325 ≤ (16603145735483/50000000000000 : ℝ)^6277 := by
    have hnat : (435514921 : ℕ)^8325*50000000000000^6277 ≤ 16603145735483^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435514921 1000000000 16603145735483 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016643849/10000000000 : ℝ)^8325 ≤ (29827414505341/100000000000000 : ℝ)^6277 := by
    have hnat : (4016643849 : ℕ)^8325*100000000000000^6277 ≤ 29827414505341^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016643849 10000000000 29827414505341 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47220247/100000000 : ℝ)^8325 ≤ (3696629401499/10000000000000 : ℝ)^6277 := by
    have hnat : (47220247 : ℕ)^8325*10000000000000^6277 ≤ 3696629401499^6277*100000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47220247 100000000 3696629401499 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435514921/1000000000 : ℝ), (4016643849/10000000000 : ℝ), (47220247/100000000 : ℝ)] ![(16603145735483/50000000000000 : ℝ), (29827414505341/100000000000000 : ℝ), (3696629401499/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435514921/1000000000 : ℝ)|^8325 ≤ (16603145735483/50000000000000 : ℝ)^6277
        have hw : |(435514921/1000000000 : ℝ)|=(435514921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016643849/10000000000 : ℝ)|^8325 ≤ (29827414505341/100000000000000 : ℝ)^6277
        have hw : |(4016643849/10000000000 : ℝ)|=(4016643849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47220247/100000000 : ℝ)|^8325 ≤ (3696629401499/10000000000000 : ℝ)^6277
        have hw : |(47220247/100000000 : ℝ)|=(47220247/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-43084977/200000000 : ℝ)*x 0 + (5159925423/10000000000 : ℝ)*x 1 + (2755110909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43084977/200000000 : ℝ)^8325 ≤ (13054792468887/100000000000000 : ℝ)^6277 := by
    have hnat : (43084977 : ℕ)^8325*100000000000000^6277 ≤ 13054792468887^6277*200000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43084977 200000000 13054792468887 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5159925423/10000000000 : ℝ)^8325 ≤ (41580283684427/100000000000000 : ℝ)^6277 := by
    have hnat : (5159925423 : ℕ)^8325*100000000000000^6277 ≤ 41580283684427^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159925423 10000000000 41580283684427 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755110909/5000000000 : ℝ)^8325 ≤ (22682461918577/50000000000000 : ℝ)^6277 := by
    have hnat : (2755110909 : ℕ)^8325*50000000000000^6277 ≤ 22682461918577^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755110909 5000000000 22682461918577 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43084977/200000000 : ℝ), (5159925423/10000000000 : ℝ), (2755110909/5000000000 : ℝ)] ![(13054792468887/100000000000000 : ℝ), (41580283684427/100000000000000 : ℝ), (22682461918577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43084977/200000000 : ℝ)|^8325 ≤ (13054792468887/100000000000000 : ℝ)^6277
        have hw : |(-43084977/200000000 : ℝ)|=(43084977/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5159925423/10000000000 : ℝ)|^8325 ≤ (41580283684427/100000000000000 : ℝ)^6277
        have hw : |(5159925423/10000000000 : ℝ)|=(5159925423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755110909/5000000000 : ℝ)|^8325 ≤ (22682461918577/50000000000000 : ℝ)^6277
        have hw : |(2755110909/5000000000 : ℝ)|=(2755110909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642107407/5000000000 : ℝ)*x 0 + (-397229933/2000000000 : ℝ)*x 1 + (5510222409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642107407/5000000000 : ℝ)^8325 ≤ (21456909180399/50000000000000 : ℝ)^6277 := by
    have hnat : (2642107407 : ℕ)^8325*50000000000000^6277 ≤ 21456909180399^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642107407 5000000000 21456909180399 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397229933/2000000000 : ℝ)^8325 ≤ (5860625664727/50000000000000 : ℝ)^6277 := by
    have hnat : (397229933 : ℕ)^8325*50000000000000^6277 ≤ 5860625664727^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397229933 2000000000 5860625664727 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510222409/10000000000 : ℝ)^8325 ≤ (45364930290289/100000000000000 : ℝ)^6277 := by
    have hnat : (5510222409 : ℕ)^8325*100000000000000^6277 ≤ 45364930290289^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510222409 10000000000 45364930290289 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642107407/5000000000 : ℝ), (-397229933/2000000000 : ℝ), (5510222409/10000000000 : ℝ)] ![(21456909180399/50000000000000 : ℝ), (5860625664727/50000000000000 : ℝ), (45364930290289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642107407/5000000000 : ℝ)|^8325 ≤ (21456909180399/50000000000000 : ℝ)^6277
        have hw : |(2642107407/5000000000 : ℝ)|=(2642107407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397229933/2000000000 : ℝ)|^8325 ≤ (5860625664727/50000000000000 : ℝ)^6277
        have hw : |(-397229933/2000000000 : ℝ)|=(397229933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510222409/10000000000 : ℝ)|^8325 ≤ (45364930290289/100000000000000 : ℝ)^6277
        have hw : |(5510222409/10000000000 : ℝ)|=(5510222409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284213487/10000000000 : ℝ)*x 0 + (5510222257/10000000000 : ℝ)*x 1 + (-1986151703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284213487/10000000000 : ℝ)^8325 ≤ (42913804067919/100000000000000 : ℝ)^6277 := by
    have hnat : (5284213487 : ℕ)^8325*100000000000000^6277 ≤ 42913804067919^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284213487 10000000000 42913804067919 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510222257/10000000000 : ℝ)^8325 ≤ (45364928630599/100000000000000 : ℝ)^6277 := by
    have hnat : (5510222257 : ℕ)^8325*100000000000000^6277 ≤ 45364928630599^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510222257 10000000000 45364928630599 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986151703/10000000000 : ℝ)^8325 ≤ (5860633640419/50000000000000 : ℝ)^6277 := by
    have hnat : (1986151703 : ℕ)^8325*50000000000000^6277 ≤ 5860633640419^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986151703 10000000000 5860633640419 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284213487/10000000000 : ℝ), (5510222257/10000000000 : ℝ), (-1986151703/10000000000 : ℝ)] ![(42913804067919/100000000000000 : ℝ), (45364928630599/100000000000000 : ℝ), (5860633640419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284213487/10000000000 : ℝ)|^8325 ≤ (42913804067919/100000000000000 : ℝ)^6277
        have hw : |(5284213487/10000000000 : ℝ)|=(5284213487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510222257/10000000000 : ℝ)|^8325 ≤ (45364928630599/100000000000000 : ℝ)^6277
        have hw : |(5510222257/10000000000 : ℝ)|=(5510222257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986151703/10000000000 : ℝ)|^8325 ≤ (5860633640419/50000000000000 : ℝ)^6277
        have hw : |(-1986151703/10000000000 : ℝ)|=(1986151703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s2_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177678969/5000000000 : ℝ)*x 0 + (4717127797/10000000000 : ℝ)*x 1 + (4021590011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177678969/5000000000 : ℝ)^8325 ≤ (33208402205217/100000000000000 : ℝ)^6277 := by
    have hnat : (2177678969 : ℕ)^8325*100000000000000^6277 ≤ 33208402205217^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177678969 5000000000 33208402205217 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4717127797/10000000000 : ℝ)^8325 ≤ (18457729803047/50000000000000 : ℝ)^6277 := by
    have hnat : (4717127797 : ℕ)^8325*50000000000000^6277 ≤ 18457729803047^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4717127797 10000000000 18457729803047 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021590011/10000000000 : ℝ)^8325 ≤ (29876138170059/100000000000000 : ℝ)^6277 := by
    have hnat : (4021590011 : ℕ)^8325*100000000000000^6277 ≤ 29876138170059^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021590011 10000000000 29876138170059 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177678969/5000000000 : ℝ), (4717127797/10000000000 : ℝ), (4021590011/10000000000 : ℝ)] ![(33208402205217/100000000000000 : ℝ), (18457729803047/50000000000000 : ℝ), (29876138170059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177678969/5000000000 : ℝ)|^8325 ≤ (33208402205217/100000000000000 : ℝ)^6277
        have hw : |(2177678969/5000000000 : ℝ)|=(2177678969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4717127797/10000000000 : ℝ)|^8325 ≤ (18457729803047/50000000000000 : ℝ)^6277
        have hw : |(4717127797/10000000000 : ℝ)|=(4717127797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021590011/10000000000 : ℝ)|^8325 ≤ (29876138170059/100000000000000 : ℝ)^6277
        have hw : |(4021590011/10000000000 : ℝ)|=(4021590011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10241/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (361/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4133/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10241/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10241/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10241/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10241/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10241/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10241/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5593/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (162514107818779/20000000000000000000 : ℝ) := by
    have hpowers : (5593/100000 : ℝ)^2081 ≤ (162514107818779/20000000000000000000 : ℝ)^512 := by
      have hnat : (5593 : ℕ)^2081*20000000000000000000^512 ≤ 162514107818779^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5593 100000 162514107818779 20000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5593/100000 : ℝ)) (X := (162514107818779/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (10241/50000 : ℝ) ^ (2081/512 : ℝ) ≤ (39723293821518599/25000000000000000000 : ℝ) := by
    have hpowers : (10241/50000 : ℝ)^2081 ≤ (39723293821518599/25000000000000000000 : ℝ)^512 := by
      have hnat : (10241 : ℕ)^2081*25000000000000000000^512 ≤ 39723293821518599^512*50000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10241 50000 39723293821518599 25000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10241/50000 : ℝ)) (X := (39723293821518599/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000162514107818779/10000000000000000000 : ℝ) ≤ (10000039984004537/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (10000162514107818779/10000000000000000000 : ℝ)^512 ≤ (10000039984004537/10000000000000000 : ℝ)^2081 := by
      have hnat : (10000162514107818779 : ℕ)^512*10000000000000000^2081 ≤ 10000039984004537^2081*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000162514107818779 10000000000000000000 10000039984004537 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039984004537/10000000000000000 : ℝ)) (X := (10000162514107818779/10000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100159705745825168291/100000000000000000000 : ℝ) ≤ (2000785393152757/2000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (100159705745825168291/100000000000000000000 : ℝ)^512 ≤ (2000785393152757/2000000000000000 : ℝ)^2081 := by
      have hnat : (100159705745825168291 : ℕ)^512*2000000000000000^2081 ≤ 2000785393152757^2081*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100159705745825168291 100000000000000000000 2000785393152757 2000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000785393152757/2000000000000000 : ℝ)) (X := (100159705745825168291/100000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12539723293821518599/12500000000000000000 : ℝ) ≤ (10007813947523033/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (12539723293821518599/12500000000000000000 : ℝ)^512 ≤ (10007813947523033/10000000000000000 : ℝ)^2081 := by
      have hnat : (12539723293821518599 : ℕ)^512*10000000000000000^2081 ≤ 10007813947523033^2081*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12539723293821518599 12500000000000000000 10007813947523033 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007813947523033/10000000000000000 : ℝ)) (X := (12539723293821518599/12500000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(162514107818779/20000000000000000000 : ℝ) ≤ ((1417591576608424793/1418000000000000000 : ℝ)+2*(11568398093/4431250000000 : ℝ)*(5593/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1417591576608424793/1418000000000000000 : ℝ)+2*(11568398093/4431250000000 : ℝ)*(5593/100000 : ℝ)=(10000039984004537/10000000000000000 : ℝ) by norm_num, show 1+2*(162514107818779/20000000000000000000 : ℝ)=(10000162514107818779/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39723293821518599/25000000000000000000 : ℝ)+(162514107818779/20000000000000000000 : ℝ) ≤ ((1417591576608424793/1418000000000000000 : ℝ)+(11568398093/4431250000000 : ℝ)*((10241/50000 : ℝ)+(5593/100000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (1417591576608424793/1418000000000000000 : ℝ)+(11568398093/4431250000000 : ℝ)*((10241/50000 : ℝ)+(5593/100000 : ℝ))=(2000785393152757/2000000000000000 : ℝ) by norm_num, show 1+(39723293821518599/25000000000000000000 : ℝ)+(162514107818779/20000000000000000000 : ℝ)=(100159705745825168291/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39723293821518599/25000000000000000000 : ℝ) ≤ ((1417591576608424793/1418000000000000000 : ℝ)+2*(11568398093/4431250000000 : ℝ)*(10241/50000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1417591576608424793/1418000000000000000 : ℝ)+2*(11568398093/4431250000000 : ℝ)*(10241/50000 : ℝ)=(10007813947523033/10000000000000000 : ℝ) by norm_num, show 1+2*(39723293821518599/25000000000000000000 : ℝ)=(12539723293821518599/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1417591576608424793/1418000000000000000 : ℝ)*(X 1 0+X 2 0)+(11568398093/4431250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (5593/100000 : ℝ)) (hi := (10241/50000 : ℝ)) (c := (1417591576608424793/1418000000000000000 : ℝ)) (alpha := (11568398093/4431250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1417591576608424793/1418000000000000000 : ℝ)*(X 0 1+X 2 1)+(11568398093/4431250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (5593/100000 : ℝ)) (hi := (10241/50000 : ℝ)) (c := (1417591576608424793/1418000000000000000 : ℝ)) (alpha := (11568398093/4431250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1417591576608424793/1418000000000000000 : ℝ)*(X 0 2+X 1 2)+(11568398093/4431250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (5593/100000 : ℝ)) (hi := (10241/50000 : ℝ)) (c := (1417591576608424793/1418000000000000000 : ℝ)) (alpha := (11568398093/4431250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86165737/400000000 : ℝ)*X 0 0+(2756356859/5000000000 : ℝ)*X 0 1+(1031491689/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687145987/5000000000 : ℝ)*X 1 0+(-2338913097/10000000000 : ℝ)*X 1 1+(5157460213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074858381/2000000000 : ℝ)*X 2 0+(2578730103/5000000000 : ℝ)*X 2 1+(-2338913197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435514921/1000000000 : ℝ)*X 0 0+(4016643849/10000000000 : ℝ)*X 0 1+(47220247/100000000 : ℝ)*X 0 2+(435514921/1000000000 : ℝ)*X 1 0+(4016643849/10000000000 : ℝ)*X 1 1+(47220247/100000000 : ℝ)*X 1 2+(435514921/1000000000 : ℝ)*X 2 0+(4016643849/10000000000 : ℝ)*X 2 1+(47220247/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-43084977/200000000 : ℝ)*X 0 0+(5159925423/10000000000 : ℝ)*X 0 1+(2755110909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642107407/5000000000 : ℝ)*X 1 0+(-397229933/2000000000 : ℝ)*X 1 1+(5510222409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284213487/10000000000 : ℝ)*X 2 0+(5510222257/10000000000 : ℝ)*X 2 1+(-1986151703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177678969/5000000000 : ℝ)*X 0 0+(4717127797/10000000000 : ℝ)*X 0 1+(4021590011/10000000000 : ℝ)*X 0 2+(2177678969/5000000000 : ℝ)*X 1 0+(4717127797/10000000000 : ℝ)*X 1 1+(4021590011/10000000000 : ℝ)*X 1 2+(2177678969/5000000000 : ℝ)*X 2 0+(4717127797/10000000000 : ℝ)*X 2 1+(4021590011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (446285792979512118024546657/70900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341457211/100000000000000 : ℝ)*(base19) + (76637599/50000000000000 : ℝ)*(base23) + (6529943/12500000000000 : ℝ)*(upper2) + (186782043/100000000000000 : ℝ)*(upper3) + (33487799/25000000000000 : ℝ)*(upper4) + (2116293550109117/100000000000000 : ℝ)*(major0) + (2116293550109117/100000000000000 : ℝ)*(major1) + (2116293550109117/100000000000000 : ℝ)*(major2) + (1407446619359229/50000000000000 : ℝ)*(sp0) + (112596255907377/4000000000000 : ℝ)*(sp1) + (1407453292933219/50000000000000 : ℝ)*(sp2) + (14176761697783/1000000000000 : ℝ)*(sp3) + (6750211589/50000000000000 : ℝ)*(sp4) + (995369731/25000000000000 : ℝ)*(sp7) + (177210018907153/12500000000000 : ℝ)*(f.failure) + (703726684785409/25000000000000 : ℝ)*(f.sum) + (11091709077903/1772500000000000000000000000 : ℝ)*base65 + (346165581038742219/141800000000000000000000000000000 : ℝ)*base68 + (73870789719657781/141800000000000000000000000000000 : ℝ)*base69 + (481498558408457781/141800000000000000000000000000000 : ℝ)*base71 + (9574721180961/3545000000000000000000000000 : ℝ)*base73 + (438395041379857781/141800000000000000000000000000000 : ℝ)*base75 + (609266666183542219/141800000000000000000000000000000 : ℝ)*base78 + (1576797677199257781/141800000000000000000000000000000 : ℝ)*base79 + (7413243167293/1772500000000000000000000000 : ℝ)*base81 + (8738151/1250000000000000000000 : ℝ)*base90 + (8738151/1250000000000000000000 : ℝ)*base92 + (8738151/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77947125686661521480959881/17725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (627084001/100000000000000 : ℝ)*(base19) + (4558001/2000000000000 : ℝ)*(base23) + (18087501/6250000000000 : ℝ)*(upper2) + (39042063/50000000000000 : ℝ)*(upper3) + (89147017/100000000000000 : ℝ)*(upper5) + (536557262007061/25000000000000 : ℝ)*(major0) + (536557262007061/25000000000000 : ℝ)*(major1) + (536557262007061/25000000000000 : ℝ)*(major2) + (2939785603/100000000000000 : ℝ)*(sp0) + (3372539107/25000000000000 : ℝ)*(sp1) + (713680355139859/25000000000000 : ℝ)*(sp4) + (2854710243104609/100000000000000 : ℝ)*(sp5) + (713681033111247/25000000000000 : ℝ)*(sp6) + (1437733589125407/100000000000000 : ℝ)*(sp7) + (1437733589125407/100000000000000 : ℝ)*(f.failure) + (1427362180172519/50000000000000 : ℝ)*(f.sum) + (23578048534523/3545000000000000000000000000 : ℝ)*base66 + (277041535478626627/35450000000000000000000000000000 : ℝ)*base68 + (342529823691823373/35450000000000000000000000000000 : ℝ)*base69 + (2335107395023373/35450000000000000000000000000000 : ℝ)*base71 + (519864511719/1772500000000000000000000000 : ℝ)*base74 + (126127416403923373/35450000000000000000000000000000 : ℝ)*base75 + (162180067086076627/35450000000000000000000000000000 : ℝ)*base78 + (135250666291073373/35450000000000000000000000000000 : ℝ)*base79 + (5971926352487/3545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (22528631/10000000000000000000000 : ℝ)*base89 + (22528631/10000000000000000000000 : ℝ)*base91 + (22528631/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1132_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10241/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1132_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1132_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1132_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1132_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (361/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4133/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
